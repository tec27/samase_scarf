//! A data structure that maps ranges to values,
//! preventing insertion of overlapping ranges.

pub struct RangeList<Key: Ord + Copy + Clone, Val> {
    ranges: Vec<(Key, Key, Val)>,
}

impl<Key: Ord + Copy + Clone, Val> RangeList<Key, Val> {
    pub fn with_capacity(cap: usize) -> RangeList<Key, Val> {
        RangeList {
            ranges: Vec::with_capacity(cap),
        }
    }

    /// Return conflicting entry on Err if any.
    pub fn add(&mut self, start: Key, end: Key, val: Val) -> Result<(), (Key, Key, &mut Val)> {
        match self.add_inner(start, end, val) {
            Ok(()) => Ok(()),
            Err(i) => {
                let existing = &mut self.ranges[i];
                Err((existing.0, existing.1, &mut existing.2))
            }
        }
    }

    /// Grows an existing range to have a a new end
    /// Return conflicting entry on Err if any.
    pub fn grow(&mut self, start: Key, end: Key, val: Val) -> Result<(), (Key, Key, &mut Val)> {
        match self.grow_inner(start, end, val) {
            Ok(()) => Ok(()),
            Err(i) => {
                let existing = &mut self.ranges[i];
                Err((existing.0, existing.1, &mut existing.2))
            }
        }
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = (Key, Key)> + 'a {
        self.ranges.iter().map(|x| (x.0, x.1))
    }

    fn grow_inner(&mut self, start: Key, end: Key, val: Val) -> Result<(), usize> {
        let index = match self.ranges.binary_search_by_key(&start, |x| x.0) {
            Ok(i) => i,
            Err(_) => return Ok(()),
        };
        if let Some(next) = self.ranges.get(index + 1) {
            if next.0 < end {
                return Err(index + 1);
            }
        }
        self.ranges[index].1 = end;
        self.ranges[index].2 = val;
        Ok(())
    }

    fn add_inner(&mut self, start: Key, end: Key, val: Val) -> Result<(), usize> {
        if self.ranges.len() == 0 {
            self.ranges.push((start, end, val));
            return Ok(());
        }
        let index = match self.ranges.binary_search_by_key(&start, |x| x.0) {
            Ok(i) => return Err(i),
            Err(i) => i,
        };
        // Check if this would overlap with previous index
        if index != 0 {
            let existing = &self.ranges[index - 1];
            if existing.1 > start {
                return Err(index - 1);
            }
        }
        // Check if this would overlap with next index
        if index != self.ranges.len() {
            let existing = &self.ranges[index];
            if existing.0 < end {
                return Err(index);
            }
        }
        self.ranges.insert(index, (start, end, val));
        Ok(())
    }
}
