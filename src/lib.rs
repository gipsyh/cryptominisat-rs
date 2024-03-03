// Copyright (c) 2016 Robert Grosse

// Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

extern crate libc;
extern crate satif;

use libc::size_t;
use satif::{Satif, SatifSat, SatifUnsat};
use std::{
    collections::HashSet,
    mem::{forget, transmute},
    slice,
    sync::Mutex,
};

/// The maximum number of variables allowed by the solver
pub const MAX_NUM_VARS: size_t = (1 << 28) - 1;

// cryptominisat types
enum SATSolver {} // opaque pointer

#[repr(C)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct Lit(u32);
impl Lit {
    /// Returns None if var >= 1 << 31, but you should not rely on var >= MAX_NUM_VARS
    pub fn new(var: u32, negated: bool) -> Option<Lit> {
        if var < (1 << 31) {
            Some(Lit(var << 1 | (negated as u32)))
        } else {
            None
        }
    }
    /// The underlying variable
    pub fn var(&self) -> u32 {
        self.0 >> 1
    }
    /// Whether this literal is negated
    pub fn isneg(&self) -> bool {
        self.0 & 1 != 0
    }
}
impl std::ops::Not for Lit {
    type Output = Lit;
    /// Negate this literal
    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

#[repr(u8)]
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Lbool {
    True = 0,
    False = 1,
    Undef = 2,
}
impl Lbool {
    pub fn from(b: bool) -> Lbool {
        if b {
            Lbool::True
        } else {
            Lbool::False
        }
    }
}

#[repr(C)]
struct slice_from_c<T>(*const T, size_t);
unsafe fn to_slice<'a, T>(raw: slice_from_c<T>) -> &'a [T] {
    slice::from_raw_parts(raw.0, raw.1)
}

#[link(name = "cryptominisat5")]
extern "C" {
    fn cmsat_new() -> *mut SATSolver;
    fn cmsat_free(this: *mut SATSolver);
    fn cmsat_nvars(this: *const SATSolver) -> u32;
    fn cmsat_add_clause(this: *mut SATSolver, lits: *const Lit, num_lits: size_t) -> bool;
    // fn cmsat_add_xor_clause(
    //     this: *mut SATSolver,
    //     vars: *const u32,
    //     num_vars: size_t,
    //     rhs: bool,
    // ) -> bool;
    fn cmsat_new_vars(this: *mut SATSolver, n: size_t);
    // fn cmsat_solve(this: *mut SATSolver) -> Lbool;
    fn cmsat_solve_with_assumptions(
        this: *mut SATSolver,
        assumptions: *const Lit,
        num_assumptions: size_t,
    ) -> Lbool;
    fn cmsat_simplify(
        this: *mut SATSolver,
        assumptions: *const Lit,
        num_assumptions: size_t,
    ) -> Lbool;
    fn cmsat_get_model(this: *const SATSolver) -> slice_from_c<Lbool>;
    fn cmsat_get_conflict(this: *const SATSolver) -> slice_from_c<Lit>;
    // fn cmsat_set_verbosity(this: *mut SATSolver, n: u32);
    // fn cmsat_set_num_threads(this: *mut SATSolver, n: u32);
    // fn cmsat_set_default_polarity(this: *mut SATSolver, polar: bool);
    // fn cmsat_set_polarity_auto(this: *mut SATSolver);
    fn cmsat_set_no_simplify(this: *mut SATSolver);
    fn cmsat_set_no_simplify_at_startup(this: *mut SATSolver);
    fn cmsat_set_no_equivalent_lit_replacement(this: *mut SATSolver);
    fn cmsat_set_no_bva(this: *mut SATSolver);
    fn cmsat_set_no_bve(this: *mut SATSolver);
    fn cmsat_set_up_for_scalmc(this: *mut SATSolver);
    fn cmsat_set_yes_comphandler(this: *mut SATSolver);
    fn cmsat_print_stats(this: *mut SATSolver);
    // fn cmsat_set_max_time(this: *mut SATSolver, max_time: f64);
}

pub struct Sat(*mut SATSolver);

impl SatifSat for Sat {
    fn lit_value(&self, lit: logic_form::Lit) -> Option<bool> {
        let solver = Solver(self.0);
        let res = match solver.get_model()[Into::<usize>::into(lit.var())] {
            Lbool::True => Some(true),
            Lbool::False => Some(false),
            Lbool::Undef => None,
        };
        forget(solver);
        res
    }
}

pub struct Unsat {
    core: Mutex<Option<HashSet<logic_form::Lit>>>,
    solver: *mut SATSolver,
}

impl SatifUnsat for Unsat {
    fn has(&self, lit: logic_form::Lit) -> bool {
        let mut core = self.core.lock().unwrap();
        if core.is_none() {
            let mut set = HashSet::new();
            let solver = Solver(self.solver);
            let conflict = solver.get_conflict();
            for l in conflict {
                let l: logic_form::Lit = unsafe { transmute(*l) };
                set.insert(!l);
            }
            forget(solver);
            *core = Some(set);
        }
        core.as_ref().unwrap().contains(&lit)
    }
}

pub struct Solver(*mut SATSolver);

impl Satif for Solver {
    type Sat = Sat;
    type Unsat = Unsat;

    fn new() -> Self {
        Solver(unsafe { cmsat_new() })
    }

    fn new_var(&mut self) -> logic_form::Var {
        let n = self.num_var();
        self.new_vars(1);
        logic_form::Var::new(n)
    }

    fn num_var(&self) -> usize {
        unsafe { cmsat_nvars(self.0) as usize }
    }

    fn add_clause(&mut self, clause: &[logic_form::Lit]) {
        let res = unsafe { cmsat_add_clause(self.0, clause.as_ptr() as *const Lit, clause.len()) };
        assert!(res);
    }

    fn solve(&mut self, assumps: &[logic_form::Lit]) -> satif::SatResult<Self::Sat, Self::Unsat> {
        match unsafe {
            cmsat_solve_with_assumptions(self.0, assumps.as_ptr() as *const Lit, assumps.len())
        } {
            Lbool::True => satif::SatResult::Sat(Sat(self.0)),
            Lbool::False => satif::SatResult::Unsat(Unsat {
                core: Mutex::new(None),
                solver: self.0,
            }),
            Lbool::Undef => todo!(),
        }
    }
}

impl Drop for Solver {
    fn drop(&mut self) {
        unsafe { cmsat_free(self.0) };
    }
}
impl Solver {
    /// Adds n new variabless.
    pub fn new_vars(&mut self, n: size_t) {
        unsafe { cmsat_new_vars(self.0, n) }
    }
    /// Returns true/false/unknown status for each variable.
    pub fn get_model(&self) -> &[Lbool] {
        unsafe { to_slice(cmsat_get_model(self.0)) }
    }
    /// Return conflicts for assumptions that led to unsatisfiability.
    pub fn get_conflict(&self) -> &[Lit] {
        unsafe { to_slice(cmsat_get_conflict(self.0)) }
    }
    pub fn set_no_simplify(&mut self) {
        unsafe { cmsat_set_no_simplify(self.0) }
    }
    pub fn set_no_simplify_at_startup(&mut self) {
        unsafe { cmsat_set_no_simplify_at_startup(self.0) }
    }
    pub fn set_no_equivalent_lit_replacement(&mut self) {
        unsafe { cmsat_set_no_equivalent_lit_replacement(self.0) }
    }
    pub fn set_no_bva(&mut self) {
        unsafe { cmsat_set_no_bva(self.0) }
    }
    pub fn set_no_bve(&mut self) {
        unsafe { cmsat_set_no_bve(self.0) }
    }
    pub fn set_up_for_scalmc(&mut self) {
        unsafe { cmsat_set_up_for_scalmc(self.0) }
    }
    pub fn print_stats(&mut self) {
        unsafe { cmsat_print_stats(self.0) }
    }

    pub fn set_yes_comphandler(&mut self) {
        unsafe { cmsat_set_yes_comphandler(self.0) }
    }

    pub fn simplify(&mut self, assumptions: &[Lit]) -> Lbool {
        unsafe { cmsat_simplify(self.0, assumptions.as_ptr(), assumptions.len()) }
    }
}
