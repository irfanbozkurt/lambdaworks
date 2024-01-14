use lambdaworks_math::field::element::FieldElement as FE;
use lambdaworks_math::field::traits::IsField;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::error::Groth16ConstraintSystemError;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct LcIndex(usize);

#[derive(Copy, Clone, PartialEq, Debug, Eq)]
pub enum Variable {
    Zero,
    One,
    Public(usize),
    Witness(usize),
    Lc(LcIndex),
}

impl Variable {
    pub fn get_lc_index(&self) -> Option<LcIndex> {
        match self {
            Variable::Lc(index) => Some(*index),
            _ => None,
        }
    }

    pub fn is_zero(&self) -> bool {
        matches!(self, Variable::Zero)
    }

    pub fn is_one(&self) -> bool {
        matches!(self, Variable::One)
    }

    pub fn is_lc(&self) -> bool {
        matches!(self, Variable::Lc(_))
    }

    pub fn is_witness_var(&self) -> bool {
        matches!(self, Variable::Witness(_))
    }

    pub fn is_public_var(&self) -> bool {
        matches!(self, Variable::Public(_))
    }
}

// The .0 is the coefficient
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LinearCombination<F: IsField>(pub Vec<(FE<F>, Variable)>);

#[derive(Debug, Clone)]
pub struct ConstraintSystem<F: IsField> {
    pub num_public_vars: usize,
    pub num_witness_vars: usize,
    pub num_constraints: usize,
    pub num_linear_combs: usize,

    pub public_assignments: Vec<FE<F>>,
    pub witness_assignments: Vec<FE<F>>,

    a_constraints: Vec<LcIndex>,
    b_constraints: Vec<LcIndex>,
    c_constraints: Vec<LcIndex>,

    lc_map: HashMap<LcIndex, LinearCombination<F>>,
    lc_assignment_cache: Rc<RefCell<HashMap<LcIndex, FE<F>>>>,
}

impl<F: IsField> ConstraintSystem<F> {
    pub fn new() -> Self {
        Self {
            num_public_vars: 1,
            num_witness_vars: 0,
            num_constraints: 0,
            num_linear_combs: 0,

            public_assignments: vec![FE::<F>::one()],
            witness_assignments: vec![],

            lc_map: HashMap::new(),
            lc_assignment_cache: Rc::new(RefCell::new(HashMap::new())),

            a_constraints: Vec::new(),
            b_constraints: Vec::new(),
            c_constraints: Vec::new(),
        }
    }

    pub fn new_input_variable(&mut self, val: FE<F>) -> Variable {
        let index = self.num_public_vars;
        self.num_public_vars += 1;

        self.public_assignments.push(val);
        Variable::Public(index)
    }

    pub fn new_witness_variable(&mut self, val: FE<F>) -> Variable {
        let index = self.num_witness_vars;
        self.num_witness_vars += 1;

        self.witness_assignments.push(val);
        Variable::Witness(index)
    }

    pub fn new_lc(&mut self, lc: LinearCombination<F>) -> Variable {
        let index = LcIndex(self.num_linear_combs);

        self.lc_map.insert(index, lc);

        self.num_linear_combs += 1;
        Variable::Lc(index)
    }

    pub fn enforce_constraint(
        &mut self,
        a: LinearCombination<F>,
        b: LinearCombination<F>,
        c: LinearCombination<F>,
    ) {
        let a_index = self.new_lc(a).get_lc_index().unwrap();
        let b_index = self.new_lc(b).get_lc_index().unwrap();
        let c_index = self.new_lc(c).get_lc_index().unwrap();
        self.a_constraints.push(a_index);
        self.b_constraints.push(b_index);
        self.c_constraints.push(c_index);

        self.num_constraints += 1;
    }

    // pub fn is_satisfied(&self) -> bool {
    //     self.which_is_unsatisfied().map(|s| s.is_none())
    // }

    /// If `self` is satisfied, outputs `Ok(None)`.
    /// If `self` is unsatisfied, outputs `Some(i)`, where `i` is the index of
    /// the first unsatisfied constraint. If `self.is_in_setup_mode()`, outputs
    /// `Err(())`.
    pub fn which_is_unsatisfied(&self) -> Result<Option<String>, Groth16ConstraintSystemError> {
        for i in 0..self.num_constraints {
            let a = self
                .eval_lc(self.a_constraints[i])
                .ok_or(Groth16ConstraintSystemError::AssignmentMissing)?;
            let b = self
                .eval_lc(self.b_constraints[i])
                .ok_or(Groth16ConstraintSystemError::AssignmentMissing)?;
            let c = self
                .eval_lc(self.c_constraints[i])
                .ok_or(Groth16ConstraintSystemError::AssignmentMissing)?;

            if a * b != c {
                return Ok(Some(String::from("Not satisfied")));
            }
        }

        Ok(None)
    }

    pub fn assigned_value(&self, v: Variable) -> Option<FE<F>> {
        match v {
            Variable::One => Some(FE::<F>::one()),
            Variable::Zero => Some(FE::<F>::zero()),
            Variable::Witness(idx) => Some((*(self.witness_assignments.get(idx)?)).clone()),
            Variable::Public(idx) => Some((*(self.public_assignments.get(idx)?)).clone()),
            Variable::Lc(idx) => match self.lc_assignment_cache.borrow().get(&idx) {
                Some(val) => Some(val.clone()),
                _ => {
                    let value = self.eval_lc(idx)?;
                    self.lc_assignment_cache
                        .borrow_mut()
                        .insert(idx, value.clone());
                    Some(value)
                }
            },
        }
    }

    fn eval_lc(&self, lc: LcIndex) -> Option<FE<F>> {
        let mut acc = FE::<F>::zero();
        for (coeff, var) in self.lc_map.get(&lc)?.0.iter() {
            acc += coeff.clone() * self.assigned_value(*var)?;
        }
        Some(acc)
    }
}

#[cfg(test)]
mod tests {
    use crate::common::*;

    use super::*;

    #[test]
    fn dummy() {
        let mut cs = ConstraintSystem::<FrField>::new();

        let _x = FrElement::from(3);
        let _sym_1 = FrElement::from(9);
        let _y = FrElement::from(27);
        let _sym_2 = FrElement::from(30);

        let _out = FrElement::from(35);

        ////

        let x = cs.new_witness_variable(_x);
        let sym_1 = cs.new_witness_variable(_sym_1);
        let y = cs.new_witness_variable(_y);
        let sym_2 = cs.new_witness_variable(_sym_2);

        let out = cs.new_input_variable(_out);

        cs.enforce_constraint(
            LinearCombination(vec![(FrElement::one(), x)]),
            LinearCombination(vec![(FrElement::one(), x)]),
            LinearCombination(vec![(FrElement::one(), sym_1)]),
        );
        cs.enforce_constraint(
            LinearCombination(vec![(FrElement::one(), sym_1)]),
            LinearCombination(vec![(FrElement::one(), x)]),
            LinearCombination(vec![(FrElement::one(), y)]),
        );
        cs.enforce_constraint(
            LinearCombination(vec![(FrElement::one(), x), (FrElement::one(), y)]),
            LinearCombination(vec![(FrElement::one(), Variable::One)]),
            LinearCombination(vec![(FrElement::one(), sym_2)]),
        );
        cs.enforce_constraint(
            LinearCombination(vec![
                (FrElement::one(), sym_2),
                (FrElement::from(5), Variable::One),
            ]),
            LinearCombination(vec![(FrElement::one(), Variable::One)]),
            LinearCombination(vec![(FrElement::one(), out)]),
        );

        println!("lol");
    }
}
