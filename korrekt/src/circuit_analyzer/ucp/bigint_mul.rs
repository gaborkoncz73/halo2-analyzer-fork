//Ez a modul a cikk BigInt-Mul szabályának Plonkish/UCP megfelelőjét valósítja meg.
//A szabály lényege: ha több zero equation együtt egy invertálható, konstans
//együtthatós lineáris rendszert alkot az ismeretlen cellákra, akkor ezek az
//ismeretlen cellák unique-k.
//
// Papíron:
//   A * x_vec - b_vec = 0
//   b_vec unique
//   A invertálható
//   ----------------
//   x_vec unique
//
//Itt ezt úgy ellenőrizzük, hogy minden equationt felbontunk egy konstans
//együtthatós A*x részre és egy K alapján unique b részre. Ezután komponensekre
//bontjuk az ismeretlen cellákat, és csak akkor tanulunk, ha létezik invertálható
//négyzetes részrendszer modulo p.

use super::{
    cell::CellId,
    expr::{UcpExpr, UcpScalar},
    facts::UcpFacts,
    rules::expression_is_unique,
};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BigIntMulInference {
    //Az a cella, amelyet a lineáris rendszer egyértelműen meghatároz
    pub cell: CellId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct UnknownLinearExpr {
    //Az ismeretlen cellák konstans field együtthatói: cella -> együttható
    terms: BTreeMap<CellId, BigInt>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LinearEquation {
    //Csak azok a tagok, amelyek még nincsenek K-ban
    unknown_terms: BTreeMap<CellId, BigInt>,
}

//BigInt-Mul szabály futtatása explicit p modulussal
pub fn infer_bigint_mul_with_modulus(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    modulus: &BigInt,
) -> Vec<BigIntMulInference> {
    if modulus <= &BigInt::from(1) {
        return Vec::new();
    }

    let equations = collect_linear_equations(expressions, facts, modulus);
    let mut inferences = BTreeSet::new();

    for component in connected_components(&equations) {
        if component.cells.is_empty() || component.equation_indices.len() < component.cells.len() {
            continue;
        }

        let matrix = coefficient_matrix(&equations, &component);
        //A rank == változószám feltétel pontosan azt jelenti, hogy a sorok között
        //van egy invertálható n x n részrendszer, vagyis a képen szereplő A.
        if rank_mod(matrix, modulus) == component.cells.len() {
            inferences.extend(component.cells);
        }
    }

    inferences
        .into_iter()
        .map(|cell| BigIntMulInference { cell })
        .collect()
}

fn collect_linear_equations(
    expressions: &[UcpExpr],
    facts: &UcpFacts,
    modulus: &BigInt,
) -> Vec<LinearEquation> {
    let mut equations = Vec::new();

    for expr in expressions {
        let Some(linear) = linearize_unknown_part(expr, facts) else {
            continue;
        };

        let mut unknown_terms = BTreeMap::new();

        for (cell, coefficient) in linear.terms {
            let coefficient = mod_field(coefficient, modulus);
            if coefficient == BigInt::from(0) {
                continue;
            }

            unknown_terms.insert(cell, coefficient);
        }

        if !unknown_terms.is_empty() {
            equations.push(LinearEquation { unknown_terms });
        }
    }

    equations
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct EquationComponent {
    //A komponensben szereplő ismeretlen cellák
    cells: Vec<CellId>,
    //Azok az equation indexek, amelyek ezekhez a cellákhoz kapcsolódnak
    equation_indices: Vec<usize>,
}

fn connected_components(equations: &[LinearEquation]) -> Vec<EquationComponent> {
    let mut equations_by_cell: BTreeMap<CellId, Vec<usize>> = BTreeMap::new();
    for (index, equation) in equations.iter().enumerate() {
        for cell in equation.unknown_terms.keys() {
            equations_by_cell
                .entry(cell.clone())
                .or_default()
                .push(index);
        }
    }

    let mut components = Vec::new();
    let mut visited_cells = HashSet::new();

    for start in equations_by_cell.keys() {
        if visited_cells.contains(start) {
            continue;
        }

        let mut cells = BTreeSet::new();
        let mut equation_indices = BTreeSet::new();
        let mut queue = VecDeque::from([start.clone()]);
        visited_cells.insert(start.clone());

        while let Some(cell) = queue.pop_front() {
            cells.insert(cell.clone());

            for equation_index in equations_by_cell.get(&cell).into_iter().flatten() {
                if !equation_indices.insert(*equation_index) {
                    continue;
                }

                for next_cell in equations[*equation_index].unknown_terms.keys() {
                    if visited_cells.insert(next_cell.clone()) {
                        queue.push_back(next_cell.clone());
                    }
                }
            }
        }

        components.push(EquationComponent {
            cells: cells.into_iter().collect(),
            equation_indices: equation_indices.into_iter().collect(),
        });
    }

    components
}

fn coefficient_matrix(
    equations: &[LinearEquation],
    component: &EquationComponent,
) -> Vec<Vec<BigInt>> {
    let cell_to_column: HashMap<CellId, usize> = component
        .cells
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, cell)| (cell, index))
        .collect();
    let mut matrix = Vec::with_capacity(component.equation_indices.len());

    for equation_index in &component.equation_indices {
        let mut row = vec![BigInt::from(0); component.cells.len()];
        for (cell, coefficient) in &equations[*equation_index].unknown_terms {
            if let Some(column) = cell_to_column.get(cell) {
                row[*column] = coefficient.clone();
            }
        }
        matrix.push(row);
    }

    matrix
}

fn rank_mod(mut matrix: Vec<Vec<BigInt>>, modulus: &BigInt) -> usize {
    if matrix.is_empty() || matrix[0].is_empty() {
        return 0;
    }

    let row_count = matrix.len();
    let column_count = matrix[0].len();
    let mut rank = 0;

    for column in 0..column_count {
        let Some(pivot_row) = (rank..row_count).find(|row| matrix[*row][column] != BigInt::from(0))
        else {
            continue;
        };

        matrix.swap(rank, pivot_row);
        let Some(inverse) = mod_inverse(&matrix[rank][column], modulus) else {
            continue;
        };

        for col in column..column_count {
            matrix[rank][col] = mod_field(&matrix[rank][col] * &inverse, modulus);
        }

        for row in 0..row_count {
            if row == rank || matrix[row][column] == BigInt::from(0) {
                continue;
            }

            let factor = matrix[row][column].clone();
            for col in column..column_count {
                matrix[row][col] = mod_field(
                    matrix[row][col].clone() - &factor * &matrix[rank][col],
                    modulus,
                );
            }
        }

        rank += 1;
        if rank == row_count {
            break;
        }
    }

    rank
}

fn mod_inverse(value: &BigInt, modulus: &BigInt) -> Option<BigInt> {
    let mut t = BigInt::from(0);
    let mut new_t = BigInt::from(1);
    let mut r = modulus.clone();
    let mut new_r = mod_field(value.clone(), modulus);

    while new_r != BigInt::from(0) {
        let quotient = &r / &new_r;

        let old_t = t;
        t = new_t.clone();
        new_t = old_t - &quotient * &new_t;

        let old_r = r;
        r = new_r.clone();
        new_r = old_r - quotient * new_r;
    }

    if r != BigInt::from(1) {
        return None;
    }

    Some(mod_field(t, modulus))
}

fn mod_field(value: BigInt, modulus: &BigInt) -> BigInt {
    let mut value = value % modulus;
    if value < BigInt::from(0) {
        value += modulus;
    }
    value
}

fn linearize_unknown_part(expr: &UcpExpr, facts: &UcpFacts) -> Option<UnknownLinearExpr> {
    //Ha az egész részexpression unique, akkor ez a b_vec oldal része lehet.
    if expression_is_unique(expr, facts) {
        return Some(UnknownLinearExpr::empty());
    }

    if let Some(value) = constant_expr_value(expr) {
        return Some(UnknownLinearExpr::constant(value));
    }

    match expr {
        UcpExpr::Var(cell) => {
            if facts.is_unique(cell) {
                Some(UnknownLinearExpr::empty())
            } else {
                Some(UnknownLinearExpr::term(cell.clone(), BigInt::from(1)))
            }
        }
        UcpExpr::Const(_) => None,
        UcpExpr::Neg(inner) => {
            linearize_unknown_part(inner, facts).map(|linear| linear.scale(BigInt::from(-1)))
        }
        UcpExpr::Add(left, right) => {
            Some(linearize_unknown_part(left, facts)?.add(linearize_unknown_part(right, facts)?))
        }
        UcpExpr::Mul(left, right) => {
            if let Some(value) = constant_expr_value(left) {
                return Some(linearize_unknown_part(right, facts)?.scale(value));
            }
            if let Some(value) = constant_expr_value(right) {
                return Some(linearize_unknown_part(left, facts)?.scale(value));
            }
            //Ha a szorzat unique, akkor már fent visszatértünk. Minden más szorzat
            //változó együtthatót vagy nemlineáris ismeretlent jelentene, ami nem A*x.
            None
        }
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => Some(UnknownLinearExpr::empty()),
            UcpScalar::Known(scale) => {
                Some(linearize_unknown_part(inner, facts)?.scale(scale.clone()))
            }
            //Absztrakt nonzero/unknown skalárral unknown cellát nem teszünk A-ba,
            //mert az A mátrix együtthatóinak konkrét field elemeknek kell lenniük.
            UcpScalar::NonZero | UcpScalar::Unknown => None,
        },
    }
}

fn constant_expr_value(expr: &UcpExpr) -> Option<BigInt> {
    match expr {
        UcpExpr::Var(_) => None,
        UcpExpr::Const(scalar) => scalar.as_known(),
        UcpExpr::Neg(inner) => Some(-constant_expr_value(inner)?),
        UcpExpr::Add(left, right) => Some(constant_expr_value(left)? + constant_expr_value(right)?),
        UcpExpr::Mul(left, right) => Some(constant_expr_value(left)? * constant_expr_value(right)?),
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => Some(BigInt::from(0)),
            UcpScalar::Known(scale) => Some(constant_expr_value(inner)? * scale),
            UcpScalar::NonZero | UcpScalar::Unknown => None,
        },
    }
}

impl UnknownLinearExpr {
    //Üres unknown részt hoz létre, vagyis az expression teljesen a b_vec oldalra kerül
    fn empty() -> Self {
        Self {
            terms: BTreeMap::new(),
        }
    }

    //Konstans expression unknown része üres
    fn constant(_value: BigInt) -> Self {
        Self::empty()
    }

    //Egyetlen változótagból álló lineáris kifejezést hoz létre
    fn term(cell: CellId, coefficient: BigInt) -> Self {
        Self {
            terms: BTreeMap::from([(cell, coefficient)]),
        }
    }

    //Két lineáris kifejezést összead, az azonos cellák együtthatóit összevonva
    fn add(mut self, other: Self) -> Self {
        for (cell, coefficient) in other.terms {
            let entry = self.terms.entry(cell).or_insert_with(|| BigInt::from(0));
            *entry += coefficient;
        }
        self.terms
            .retain(|_, coefficient| coefficient != &BigInt::from(0));
        self
    }

    //Az egész lineáris kifejezést megszorozza egy konstanssal
    fn scale(mut self, scalar: BigInt) -> Self {
        for coefficient in self.terms.values_mut() {
            *coefficient *= &scalar;
        }
        self.terms
            .retain(|_, coefficient| coefficient != &BigInt::from(0));
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn modulus() -> BigInt {
        BigInt::from(101)
    }

    fn add3(left: UcpExpr, middle: UcpExpr, right: UcpExpr) -> UcpExpr {
        UcpExpr::add(UcpExpr::add(left, middle), right)
    }

    //Ellenőrzi, hogy egy invertálható 2x2 lineáris rendszerből mindkét ismeretlen unique lesz
    #[test]
    fn infers_unknowns_from_invertible_linear_system() {
        let a = CellId::instance(0, 0);
        let b = CellId::instance(1, 0);
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let facts = UcpFacts::from_iter([a.clone(), b.clone()]);
        let expressions = vec![
            add3(
                UcpExpr::var(x.clone()),
                UcpExpr::var(y.clone()),
                UcpExpr::neg(UcpExpr::var(a)),
            ),
            add3(
                UcpExpr::var(x.clone()),
                UcpExpr::neg(UcpExpr::var(y.clone())),
                UcpExpr::neg(UcpExpr::var(b)),
            ),
        ];

        let inferences = infer_bigint_mul_with_modulus(&expressions, &facts, &modulus());

        assert_eq!(
            inferences,
            vec![
                BigIntMulInference { cell: x },
                BigIntMulInference { cell: y },
            ]
        );
    }

    //Ellenőrzi, hogy szinguláris mátrixból nem következtetünk uniqueness-t
    #[test]
    fn does_not_fire_for_singular_matrix() {
        let a = CellId::instance(0, 0);
        let b = CellId::instance(1, 0);
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let facts = UcpFacts::from_iter([a.clone(), b.clone()]);
        let expressions = vec![
            add3(
                UcpExpr::var(x.clone()),
                UcpExpr::var(y.clone()),
                UcpExpr::neg(UcpExpr::var(a)),
            ),
            UcpExpr::add(
                UcpExpr::add(
                    UcpExpr::scale_by(UcpExpr::var(x), UcpScalar::known_i64(2)),
                    UcpExpr::scale_by(UcpExpr::var(y), UcpScalar::known_i64(2)),
                ),
                UcpExpr::neg(UcpExpr::var(b)),
            ),
        ];

        assert!(infer_bigint_mul_with_modulus(&expressions, &facts, &modulus()).is_empty());
    }

    //Ellenőrzi, hogy ha nincs elég független equation, akkor nem következtetünk
    #[test]
    fn does_not_fire_when_rhs_contains_unconstrained_cell() {
        let a = CellId::instance(0, 0);
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let z = CellId::advice(2, 0);
        let facts = UcpFacts::from_iter([a.clone()]);
        let expressions = vec![
            add3(
                UcpExpr::var(x),
                UcpExpr::var(y.clone()),
                UcpExpr::neg(UcpExpr::var(z)),
            ),
            UcpExpr::add(UcpExpr::var(y), UcpExpr::neg(UcpExpr::var(a))),
        ];

        assert!(infer_bigint_mul_with_modulus(&expressions, &facts, &modulus()).is_empty());
    }

    //Ellenőrzi, hogy sparse 3x3 teljes rangú rendszerre is működik
    #[test]
    fn infers_sparse_full_rank_component() {
        let a = CellId::instance(0, 0);
        let b = CellId::instance(1, 0);
        let c = CellId::instance(2, 0);
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let z = CellId::advice(2, 0);
        let facts = UcpFacts::from_iter([a.clone(), b.clone(), c.clone()]);
        let expressions = vec![
            add3(
                UcpExpr::var(x.clone()),
                UcpExpr::var(y.clone()),
                UcpExpr::neg(UcpExpr::var(a)),
            ),
            add3(
                UcpExpr::var(y.clone()),
                UcpExpr::var(z.clone()),
                UcpExpr::neg(UcpExpr::var(b)),
            ),
            add3(
                UcpExpr::var(x.clone()),
                UcpExpr::var(z.clone()),
                UcpExpr::neg(UcpExpr::var(c)),
            ),
        ];

        let inferences = infer_bigint_mul_with_modulus(&expressions, &facts, &modulus());

        assert_eq!(
            inferences,
            vec![
                BigIntMulInference { cell: x },
                BigIntMulInference { cell: y },
                BigIntMulInference { cell: z },
            ]
        );
    }

    //Ellenőrzi, hogy a b_vec oldal lehet összetett, ha K alapján unique
    #[test]
    fn accepts_unique_nonlinear_rhs_expression() {
        let a = CellId::instance(0, 0);
        let b = CellId::instance(1, 0);
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let facts = UcpFacts::from_iter([a.clone(), b.clone()]);
        let expressions = vec![
            add3(
                UcpExpr::var(x.clone()),
                UcpExpr::var(y.clone()),
                UcpExpr::mul(UcpExpr::var(a.clone()), UcpExpr::var(b)),
            ),
            add3(
                UcpExpr::var(x.clone()),
                UcpExpr::neg(UcpExpr::var(y.clone())),
                UcpExpr::var(a),
            ),
        ];

        let inferences = infer_bigint_mul_with_modulus(&expressions, &facts, &modulus());

        assert_eq!(
            inferences,
            vec![
                BigIntMulInference { cell: x },
                BigIntMulInference { cell: y },
            ]
        );
    }

    //Ellenőrzi, hogy unique, de nem konkrét konstans együtthatót nem teszünk az A mátrixba
    #[test]
    fn rejects_unique_variable_coefficient() {
        let a = CellId::instance(0, 0);
        let b = CellId::instance(1, 0);
        let c = CellId::instance(2, 0);
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let facts = UcpFacts::from_iter([a.clone(), b.clone(), c.clone()]);
        let expressions = vec![
            add3(
                UcpExpr::mul(UcpExpr::var(a), UcpExpr::var(x.clone())),
                UcpExpr::var(y.clone()),
                UcpExpr::neg(UcpExpr::var(b)),
            ),
            add3(
                UcpExpr::var(x),
                UcpExpr::neg(UcpExpr::var(y)),
                UcpExpr::neg(UcpExpr::var(c)),
            ),
        ];

        assert!(infer_bigint_mul_with_modulus(&expressions, &facts, &modulus()).is_empty());
    }

    //Ellenőrzi, hogy extra equation mellett is elég, ha létezik invertálható négyzetes részrendszer
    #[test]
    fn accepts_invertible_square_subsystem_with_extra_equation() {
        let a = CellId::instance(0, 0);
        let b = CellId::instance(1, 0);
        let c = CellId::instance(2, 0);
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        let facts = UcpFacts::from_iter([a.clone(), b.clone(), c.clone()]);
        let expressions = vec![
            add3(
                UcpExpr::var(x.clone()),
                UcpExpr::var(y.clone()),
                UcpExpr::neg(UcpExpr::var(a)),
            ),
            add3(
                UcpExpr::var(x.clone()),
                UcpExpr::neg(UcpExpr::var(y.clone())),
                UcpExpr::neg(UcpExpr::var(b)),
            ),
            add3(
                UcpExpr::scale_by(UcpExpr::var(x.clone()), UcpScalar::known_i64(2)),
                UcpExpr::var(y.clone()),
                UcpExpr::neg(UcpExpr::var(c)),
            ),
        ];

        let inferences = infer_bigint_mul_with_modulus(&expressions, &facts, &modulus());

        assert_eq!(
            inferences,
            vec![
                BigIntMulInference { cell: x },
                BigIntMulInference { cell: y },
            ]
        );
    }
}
