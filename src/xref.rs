use crate::shape::*;
use std::{collections::HashMap, ops::Deref};

pub trait NamedShape {
    fn name(&self) -> &str;
    fn shape(&self) -> &Expression;
}

impl<T> NamedShape for (T, Expression)
where
    T: AsRef<str>,
{
    fn name(&self) -> &str {
        self.0.as_ref()
    }

    fn shape(&self) -> &Expression {
        &self.1
    }
}

#[derive(Debug)]
pub enum Error {
    IncorrectExpression(String),
}

pub struct XRef<'a> {
    gid_map: HashMap<i32, (&'a Expression, Option<&'a str>)>,
    name_map: HashMap<&'a str, &'a Expression>,
}

impl<'a> XRef<'a> {
    pub fn new<I, T>(types: I) -> Result<Self, Error>
    where
        I: IntoIterator<Item = &'a T>,
        T: 'a + NamedShape,
    {
        let mut gid_map = HashMap::new();
        let mut name_map = HashMap::new();
        let mut gid_name = HashMap::new();
        for ty in types {
            if let Expression::Top_app(Group { gid, .. }, ..) = ty.shape() {
                name_map.insert(ty.name(), ty.shape());
                gid_name.insert(*gid, ty.name());
            } else {
                return Err(Error::IncorrectExpression(format!(
                    "Wrong type for {name}",
                    name = ty.name()
                )));
            }
        }

        struct GidVisitor<'a, 'b: 'a> {
            gid_name: HashMap<Gid, &'b str>,
            gid_map: &'a mut HashMap<Gid, (&'b Expression, Option<&'b str>)>,
        }

        impl<'a, 'b> Visitor<'b> for GidVisitor<'a, 'b> {
            fn apply(&mut self, expr: &'b Expression) {
                if let Expression::Top_app(group, ..) = expr {
                    if self.gid_map.contains_key(&group.gid) {
                        return;
                    }
                    let name = self.gid_name.get(&group.gid).map(|n| *n);
                    self.gid_map.insert(group.gid, (expr, name));
                }
                expr.visit(self)
            }
        }

        let mut visitor = GidVisitor {
            gid_name,
            gid_map: &mut gid_map,
        };

        name_map.values().for_each(|expr| visitor.apply(expr));

        let result = Self { gid_map, name_map };
        Ok(result)
    }

    /// Returns top expression (`[Expression::Top_app]`) registered for the provided `name`.
    pub fn for_name(&'a self, name: &str) -> Option<&'a Expression> {
        self.name_map.get(name).map(Deref::deref)
    }

    /// Returns a pair of `[Expression]` and optional name for the specified `gid`.
    pub fn for_gid(&self, gid: Gid) -> Option<(&'a Expression, Option<&'a str>)> {
        self.gid_map.get(&gid).map(|t| *t)
    }
}

#[cfg(test)]
mod tests {
    use crate::shape::{Expression, Group};

    use super::XRef;

    /// Wraps `expr` into `[Expression::Top_app]`.
    fn wrap(expr: Expression, gid: i32) -> Expression {
        let tid = "t".to_string();
        Expression::Top_app(
            Group {
                gid,
                loc: "__loc".to_string(),
                members: vec![(tid.clone(), (vec![], expr))],
            },
            tid.clone(),
            vec![],
        )
    }

    #[test]
    fn new_ok() {
        let exprs = vec![(
            "my_type",
            wrap(Expression::new_base("base_type".to_string(), vec![]), 0),
        )];
        assert!(XRef::new(&exprs).is_ok());
    }

    #[test]
    fn new_err() {
        let exprs = vec![(
            "my_type",
            Expression::new_base("base_type".to_string(), vec![]),
        )];
        assert!(XRef::new(&exprs).is_err());
    }

    #[test]
    fn for_gid() {
        let gid = 0;
        let exprs = vec![(
            "my_type",
            wrap(Expression::new_base("base_type".to_string(), vec![]), gid),
        )];
        let xref = XRef::new(&exprs).unwrap();
        assert!(xref.for_gid(gid).is_some());
        assert!(xref.for_gid(gid + 1).is_none());
    }

    #[test]
    fn for_name() {
        let exprs = vec![(
            "my_type",
            wrap(Expression::new_base("base_type".to_string(), vec![]), 0),
        )];
        let xref = XRef::new(&exprs).unwrap();
        assert!(xref.for_name("my_type").is_some());
        assert!(xref.for_name("other_type").is_none());
    }

}
