use std::fmt;

pub struct Indented<'a, T> {
    f: &'a mut T,
    level: u32,
    indentation: String,
}

impl<'a, T> Indented<'a, T> {
    pub fn new(f: &'a mut T, indentation: impl Into<String>) -> Self {
        Self {
            f,
            level: 0,
            indentation: indentation.into(),
        }
    }
    pub fn indent(&mut self, inc: u32) {
        self.level += inc;
    }
    pub fn dedent(&mut self, inc: u32) {
        self.level -= inc;
    }
}

impl<'a, T: fmt::Write> fmt::Write for Indented<'a, T> {
    fn write_str(&mut self, input: &str) -> fmt::Result {
        let mut it = input.split('\n');
        if let Some(line) = it.next() {
            self.f.write_str(line)?;
        }
        for line in it {
            self.f.write_char('\n')?;
            for _ in 0..self.level {
                self.f.write_str(&self.indentation)?;
            }
            self.f.write_str(line)?;
        }
        Ok(())
    }

    fn write_fmt(&mut self, args: fmt::Arguments<'_>) -> fmt::Result {
        self.write_str(&args.to_string())
    }
}
