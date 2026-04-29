use std::collections::HashMap;

use std::hash::Hash;
use std::cmp::Eq;

pub enum AssignmentError {
    InverseEnabledAfterAssignment
}

pub struct Assignment<'a, T: Hash + Eq, const N: usize> {
    assignment: HashMap<[&'a T; N], usize>,
    inv_assignment: Option<Vec<[&'a T; N]>>,
    curr: usize,
    offset: usize,
    has_assigned: Vec<usize>
} 

impl<'a, T: Hash + Eq, const N: usize> Assignment<'a, T, N> {

    pub fn new(offset: usize) -> Self {
        Assignment { assignment: HashMap::new(), inv_assignment: None, curr: 0, offset: offset, has_assigned: Vec::new() }
    }

    pub fn get_offset(&self) -> usize {
        self.offset
    }

    pub fn enable_inverse(&mut self) -> Result<(), AssignmentError> {
        if self.curr != 0 {
            Err(AssignmentError::InverseEnabledAfterAssignment)
        } else {
            self.inv_assignment = Some(Vec::new());
            Ok(())
        }
    }

    pub fn len(&self) -> usize {
        self.curr
    }

    fn get_assignment_with_curr(&mut self, input: [&'a T; N], curr: usize) -> (usize, bool) {

        let new_insert = !self.assignment.contains_key(&input);
        if new_insert {
            self.assignment.insert(input, curr + self.offset);
            if let Some(inv_assignment) = &mut self.inv_assignment {inv_assignment.push(input.clone());}
            self.has_assigned.push(curr);
        }

        (self.assignment[&input], new_insert)
    }

    pub fn get_assignment(&mut self, input: [&'a T; N]) -> usize {

        let (assignment, new_insert) = self.get_assignment_with_curr(input, self.curr);

        if new_insert {self.curr += 1;}
        assignment
    }
    
    pub fn get_inv_assignment(&self, inverse: usize) -> Option<[&'a T; N]> {
        if let Some(inv_assignment) = &self.inv_assignment {Some(inv_assignment[inverse - self.offset])}
        else {None}
    }
}