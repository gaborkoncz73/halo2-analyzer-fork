// A már ismert Delta alapján konkrét értékeket és lefedő domaineket vezet le.
// Következtetési javaslatokat ad; a globális állapotot nem módosítja.
//A beolvasztást, a K frissítését és az új propagációs köröket az engine végzi.

use super::{
    bounded_value, domain_values, evaluate_expr, finite_domain_from_values, normalize_field_value,
    normalize_value, value_kind_with_optional_modulus, CellId, UcpExpr, UcpScalar, UcpValueDomain,
    UcpValueFacts, ValueKind, MAX_FINITE_DOMAIN_SIZE,
};
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

#[path = "linear_domains.rs"]
mod linear_domains;
pub(crate) use linear_domains::LinearDomains;

// A lineáris keresésben külön korlátozza a cellák és az egyenletek számát.
pub(super) const MAX_LINEAR_SYSTEM_CELLS: usize = 64;
pub(super) const MAX_LINEAR_SYSTEM_EQUATIONS: usize = 256;

// A numerikus lineáris kifejezést konstans taggal és cellaegyütthatókkal reprezentálja.
//A terms a numerikusan még ismeretlen cellák együtthatóit tárolja, a K-tagságuktól függetlenül.
#[derive(Clone, Debug, Eq, PartialEq)]
struct LinearExpr {
    constant: BigInt,
    terms: HashMap<CellId, BigInt>,
}

//Nullával egyenlő kifejezésből cellák lefedő domainjeire következtet, modulus nélkül.
pub fn infer_value_domains_from_zero_equation(
    expr: &UcpExpr,
    values: &UcpValueFacts,
) -> Vec<(CellId, UcpValueDomain)> {
    infer_value_domains_from_zero_equation_with_optional_modulus(expr, values, None)
}

//Nullával egyenlő kifejezésből cellák lefedő domainjeire következtet a test modulusa szerint.
pub fn infer_value_domains_from_zero_equation_with_modulus(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: &BigInt,
) -> Vec<(CellId, UcpValueDomain)> {
    infer_value_domains_from_zero_equation_with_optional_modulus(expr, values, Some(field_modulus))
}

//Összegyűjti a gyökhalmaz-, értékadási, lineáris és számjegyfelbontási következtetéseket.
//Csak javaslatokat ad; a beolvasztást, K-frissítést és újrafuttatást az engine végzi.
fn infer_value_domains_from_zero_equation_with_optional_modulus(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Vec<(CellId, UcpValueDomain)> {
    let mut inferences = Vec::new();

    // A szorzat tényezőinek gyökeiből véges lefedő domaint készít.
    if let Some((root_expr, domain)) = infer_root_expression_domain(expr, values, field_modulus) {
        for (cell, domain) in infer_domains_from_expression_domain_with_optional_modulus(
            root_expr,
            &domain,
            values,
            field_modulus,
        ) {
            push_domain_inference(&mut inferences, cell, domain);
        }
    }

    // Az Assign értékvisszaállító változatával c*x-e=0 alakból számol, ha e értéke ismert.
    if let Some((cell, value)) = infer_from_zero_expr(expr, values, field_modulus) {
        push_domain_inference(&mut inferences, cell, UcpValueDomain::exact(value));
    }

    // Az Assign domainváltozatával c*x-e=0 alakból jelölthalmazt képez, ha Delta(e) véges.
    for (cell, domain) in infer_linear_domains(expr, values, field_modulus) {
        push_domain_inference(&mut inferences, cell, domain);
    }

    // A Base-Conv alak számjegykorlátaiból a csomagolt cella domainjére következtet.
    for (cell, domain) in infer_base_conv_value_domains(expr, values, field_modulus) {
        push_domain_inference(&mut inferences, cell, domain);
    }

    inferences
}

//Csak a konkrét értékű következtetéseket adja vissza
pub fn infer_value_assignments_from_zero_equation(
    expr: &UcpExpr,
    values: &UcpValueFacts,
) -> Vec<(CellId, BigInt)> {
    infer_value_domains_from_zero_equation(expr, values)
        .into_iter()
        .filter_map(|(cell, domain)| match domain {
            UcpValueDomain::Exact(value) => Some((cell, value)),
            UcpValueDomain::FiniteSet(_) => None,
        })
        .collect()
}

//Konstans együtthatós rendszereket old meg Delta számára, akkor is, ha a cellák már K-ban vannak.
// A mátrixos értékvisszaállítás különbözik a puszta egyértelműségi teszttől:
// a megoldott részrendszer konkrét testbeli értékeit adja vissza a Deltához.
pub fn infer_linear_system_values_with_modulus(
    expressions: &[UcpExpr],
    values: &UcpValueFacts,
    modulus: &BigInt,
) -> Vec<(CellId, BigInt)> {
    if modulus <= &BigInt::from(1) {
        return Vec::new();
    }

    let mut equations = Vec::new();
    let mut equations_by_cell: BTreeMap<CellId, Vec<usize>> = BTreeMap::new();
    for expr in expressions {
        let Some(mut linear) = linearize_field_system(expr, values) else {
            continue;
        };
        linear.constant = mod_field(linear.constant, modulus);
        for coefficient in linear.terms.values_mut() {
            *coefficient = mod_field(coefficient.clone(), modulus);
        }
        linear
            .terms
            .retain(|_, coefficient| coefficient != &BigInt::from(0));
        if linear.terms.is_empty() {
            if linear.constant != BigInt::from(0) {
                return Vec::new();
            }
            continue;
        }
        let index = equations.len();
        for cell in linear.terms.keys() {
            equations_by_cell
                .entry(cell.clone())
                .or_default()
                .push(index);
        }
        equations.push(linear);
    }

    //Azonos változóhalmazú, teljes rangú részrendszer akkor is oldható lehet, ha máshol szabad cellák vannak.
    let mut groups: BTreeMap<Vec<CellId>, Vec<usize>> = BTreeMap::new();
    for (index, equation) in equations
        .iter()
        .enumerate()
        .take(MAX_LINEAR_SYSTEM_EQUATIONS)
    {
        if !(2..=MAX_LINEAR_SYSTEM_CELLS).contains(&equation.terms.len()) {
            continue;
        }
        let mut cells: Vec<_> = equation.terms.keys().cloned().collect();
        cells.sort();
        groups.entry(cells).or_default().push(index);
    }
    let mut inferences = BTreeMap::new();
    for (cells, indices) in groups {
        if indices.len() >= cells.len() && indices.len() <= MAX_LINEAR_SYSTEM_EQUATIONS {
            inferences.extend(solve_linear_subsystem(
                &equations, &indices, &cells, values, modulus,
            ));
        }
    }
    // A független komponenseket külön oldja meg.
    let mut visited = HashSet::new();
    for start in equations_by_cell.keys() {
        if !visited.insert(start.clone()) {
            continue;
        }
        let mut queue = VecDeque::from([start.clone()]);
        let mut cells = BTreeSet::new();
        let mut indices = BTreeSet::new();
        while let Some(cell) = queue.pop_front() {
            cells.insert(cell.clone());
            for index in &equations_by_cell[&cell] {
                if indices.insert(*index) {
                    for next in equations[*index].terms.keys() {
                        if visited.insert(next.clone()) {
                            queue.push_back(next.clone());
                        }
                    }
                }
            }
        }
        if cells.len() > MAX_LINEAR_SYSTEM_CELLS
            || indices.len() > MAX_LINEAR_SYSTEM_EQUATIONS
            || indices.len() < cells.len()
        {
            continue;
        }

        let cells: Vec<_> = cells.into_iter().collect();
        inferences.extend(solve_linear_subsystem(
            &equations,
            &indices.into_iter().collect::<Vec<_>>(),
            &cells,
            values,
            modulus,
        ));
    }
    inferences
        .into_iter()
        .filter(|(cell, _)| !values.domain_is_complete(cell))
        .collect()
}

fn solve_linear_subsystem(
    equations: &[LinearExpr],
    indices: &[usize],
    cells: &[CellId],
    values: &UcpValueFacts,
    modulus: &BigInt,
) -> Vec<(CellId, BigInt)> {
    let matrix = indices
        .iter()
        .map(|index| {
            let equation = &equations[*index];
            let mut row: Vec<_> = cells
                .iter()
                .map(|cell| {
                    equation
                        .terms
                        .get(cell)
                        .cloned()
                        .unwrap_or_else(|| BigInt::from(0))
                })
                .collect();
            row.push(mod_field(-equation.constant.clone(), modulus));
            row
        })
        .collect();
    let Some(solution) = solve_field_system(matrix, cells.len(), modulus) else {
        return Vec::new();
    };
    // Csak a már igazolt domainekkel összeegyeztethető megoldást adja vissza.
    if cells.iter().zip(&solution).any(|(cell, value)| {
        values.domain(cell).is_some_and(|domain| {
            !domain_values(domain)
                .iter()
                .any(|candidate| mod_field(candidate.clone(), modulus) == *value)
        })
    }) {
        return Vec::new();
    }
    cells
        .iter()
        .cloned()
        .zip(solution)
        .filter_map(|(cell, value)| {
            normalize_field_value(value, modulus).map(|value| (cell, value))
        })
        .collect()
}

fn solve_field_system(
    mut matrix: Vec<Vec<BigInt>>,
    columns: usize,
    modulus: &BigInt,
) -> Option<Vec<BigInt>> {
    //Gauss-Jordan-elimináció a testben: a pivot osztása moduláris inverzzel történik.
    for column in 0..columns {
        let pivot = (column..matrix.len()).find(|row| matrix[*row][column] != BigInt::from(0))?;
        matrix.swap(column, pivot);
        let inverse = mod_inverse(&matrix[column][column], modulus)?;
        for entry in &mut matrix[column][column..=columns] {
            *entry = mod_field(entry.clone() * &inverse, modulus);
        }
        for row in 0..matrix.len() {
            if row == column || matrix[row][column] == BigInt::from(0) {
                continue;
            }
            let factor = matrix[row][column].clone();
            for col in column..=columns {
                matrix[row][col] = mod_field(
                    matrix[row][col].clone() - &factor * &matrix[column][col],
                    modulus,
                );
            }
        }
    }
    //A maradék sorokban az összes együttható nulla; nemnulla jobb oldal ellentmondást jelent.
    if matrix[columns..]
        .iter()
        .any(|row| row[columns] != BigInt::from(0))
    {
        return None;
    }
    Some(
        (0..columns)
            .map(|column| matrix[column][columns].clone())
            .collect(),
    )
}

fn linearize_field_system(expr: &UcpExpr, values: &UcpValueFacts) -> Option<LinearExpr> {
    // Teljes testelemekkel számolja az együtthatókat; a végső Delta-értéket méretkorláttal ellenőrzi.
    //Az ismert cellákat konstansra cseréli, de két numerikusan ismeretlen tényezőt nem linearizál.
    match expr {
        UcpExpr::Var(cell) => Some(match values.known_value(cell) {
            Some(value) => LinearExpr::constant(value.clone()),
            None => LinearExpr::term(cell.clone(), BigInt::from(1)),
        }),
        UcpExpr::Const(scalar) => Some(LinearExpr::constant(scalar.as_known()?)),
        UcpExpr::Neg(inner) => Some(linearize_field_system(inner, values)?.scale(BigInt::from(-1))),
        UcpExpr::Add(left, right) => {
            Some(linearize_field_system(left, values)?.add(linearize_field_system(right, values)?))
        }
        UcpExpr::Mul(left, right) => {
            let left = linearize_field_system(left, values)?;
            let right = linearize_field_system(right, values)?;
            if left.terms.is_empty() {
                Some(right.scale(left.constant))
            } else if right.terms.is_empty() {
                Some(left.scale(right.constant))
            } else {
                None
            }
        }
        UcpExpr::Scale(_, UcpScalar::Zero) => Some(LinearExpr::constant(BigInt::from(0))),
        UcpExpr::Scale(inner, scalar) => {
            Some(linearize_field_system(inner, values)?.scale(scalar.as_known()?))
        }
    }
}

// Külső kifejezésdomainből a bemeneti cellák domainjére következtet.
// Például 2*x+1 lookup-bemenetnél az ismert halmazt x értékeire vetíti vissza.
// Az eredmény továbbra is lefedő halmaz; nem tanúsítja a jelöltek megvalósíthatóságát.
pub fn infer_domains_from_expression_domain(
    expr: &UcpExpr,
    expr_domain: &UcpValueDomain,
    values: &UcpValueFacts,
) -> Vec<(CellId, UcpValueDomain)> {
    infer_domains_from_expression_domain_with_optional_modulus(expr, expr_domain, values, None)
}

// A visszavetítésben a nemnulla együtthatóval testbeli inverzen keresztül oszt.
pub fn infer_domains_from_expression_domain_with_modulus(
    expr: &UcpExpr,
    expr_domain: &UcpValueDomain,
    values: &UcpValueFacts,
    field_modulus: &BigInt,
) -> Vec<(CellId, UcpValueDomain)> {
    infer_domains_from_expression_domain_with_optional_modulus(
        expr,
        expr_domain,
        values,
        Some(field_modulus),
    )
}

fn infer_domains_from_expression_domain_with_optional_modulus(
    expr: &UcpExpr,
    expr_domain: &UcpValueDomain,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Vec<(CellId, UcpValueDomain)> {
    let Some(linear) = linearize(expr, values) else {
        return Vec::new();
    };

    let mut inferences = Vec::new();

    for (cell, coefficient) in &linear.terms {
        if coefficient == &BigInt::from(0) || values.domain_is_complete(cell) {
            continue;
        }

        let Some(domain) = solve_linear_domain_for_cell_with_rhs(
            &linear,
            cell,
            coefficient,
            expr_domain,
            values,
            field_modulus,
        ) else {
            continue;
        };

        push_domain_inference(&mut inferences, cell.clone(), domain);
    }

    inferences
}

fn push_domain_inference(
    inferences: &mut Vec<(CellId, UcpValueDomain)>,
    cell: CellId,
    domain: UcpValueDomain,
) {
    if let Some((_, existing_domain)) = inferences
        .iter_mut()
        .find(|(existing_cell, _)| existing_cell == &cell)
    {
        if let Some(intersection) = existing_domain.intersect(&domain) {
            *existing_domain = intersection;
        }
    } else {
        inferences.push((cell, domain));
    }
}

//Root: a már szorzatalakban szereplő, közös affin részt tartalmazó tényezőket vizsgálja.
//A visszaadott domain az első tényező kifejezésére vonatkozik; a cellákra vetítés később történik.
pub(super) fn infer_root_expression_domain<'a>(
    expr: &'a UcpExpr,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Option<(&'a UcpExpr, UcpValueDomain)> {
    let mut factors = Vec::new();
    collect_product_factors(expr, &mut factors, field_modulus);

    if factors.len() < 2 {
        return None;
    }

    let first = *factors.first()?;
    let common = linearize(first, values)?;
    if common.terms.is_empty() {
        return None;
    }
    let mut roots = Vec::new();

    for factor in factors {
        let linear = linearize(factor, values)?;
        // Az e-c és c-e alakot is kezeli, így az átvett polinomiális tartományellenőrzőt is felismeri.
        if linear.terms == common.terms {
            roots.push(&common.constant - linear.constant);
        } else if linear.terms.len() == common.terms.len()
            && linear.terms.iter().all(|(cell, coefficient)| {
                common
                    .terms
                    .get(cell)
                    .is_some_and(|other| coefficient == &-other)
            })
        {
            roots.push(&common.constant + linear.constant);
        } else {
            return None;
        }
    }

    Some((first, finite_domain_from_values(roots, field_modulus)?))
}

//Meglévő szorzáscsomópontokat lapít, nem kifejtett polinomokat faktorizál.
//Például: [x,x-1,x-2]
fn collect_product_factors<'a>(
    expr: &'a UcpExpr,
    factors: &mut Vec<&'a UcpExpr>,
    modulus: Option<&BigInt>,
) {
    match expr {
        UcpExpr::Mul(left, right) => {
            collect_product_factors(left, factors, modulus);
            collect_product_factors(right, factors, modulus);
        }
        UcpExpr::Neg(inner) => collect_product_factors(inner, factors, modulus),
        UcpExpr::Scale(_, UcpScalar::Known(scale)) if scale == &BigInt::from(0) => {
            factors.push(expr)
        }
        UcpExpr::Scale(inner, scalar) if scalar.is_non_zero_with_modulus(modulus) => {
            collect_product_factors(inner, factors, modulus)
        }
        //Nullatényezőnél az egyenlet azonosság; elhagyása hamis korlátozást adhatna.
        UcpExpr::Scale(_, UcpScalar::Zero) => factors.push(expr),
        _ => factors.push(expr),
    }
}

//Assign előszűrő: nemnulla szorzótényezők mellett konkrét cellaértéket tanul
fn infer_from_zero_expr(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    modulus: Option<&BigInt>,
) -> Option<(CellId, BigInt)> {
    match expr {
        UcpExpr::Scale(_, UcpScalar::Known(scale)) if scale == &BigInt::from(0) => None,
        UcpExpr::Mul(left, right) => match (
            value_kind_with_optional_modulus(left, values, modulus),
            value_kind_with_optional_modulus(right, values, modulus),
        ) {
            (ValueKind::NonZero, _) => infer_from_zero_expr(right, values, modulus),
            (_, ValueKind::NonZero) => infer_from_zero_expr(left, values, modulus),
            (ValueKind::Zero, _) | (_, ValueKind::Zero) => None,
            _ => infer_linear_assignment(expr, values, modulus),
        },
        UcpExpr::Scale(inner, scalar) if scalar.is_non_zero_with_modulus(modulus) => {
            infer_from_zero_expr(inner, values, modulus)
        }
        UcpExpr::Scale(_, UcpScalar::Zero) => None,
        _ => infer_linear_assignment(expr, values, modulus),
    }
}

// Az Assign konkrétérték-változatával lineáris null-egyenletet old meg egy ismeretlen cellára.
fn infer_linear_assignment(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    modulus: Option<&BigInt>,
) -> Option<(CellId, BigInt)> {
    let linear = linearize(expr, values)?;

    if linear.terms.len() != 1 {
        return None;
    }

    let (cell, coefficient) = linear.terms.into_iter().next().unwrap();
    if coefficient == BigInt::from(0) || values.domain_is_complete(&cell) {
        return None;
    }

    let numerator = -linear.constant;
    Some((cell, solve_linear_value(&numerator, &coefficient, modulus)?))
}

// Az Assign domainváltozatával lineáris null-egyenletből véges domaint képez célcellákra.
fn infer_linear_domains(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Vec<(CellId, UcpValueDomain)> {
    let Some(linear) = linearize(expr, values) else {
        return Vec::new();
    };

    let mut inferences = Vec::new();

    for (cell, coefficient) in &linear.terms {
        if coefficient == &BigInt::from(0) || values.domain_is_complete(cell) {
            continue;
        }

        let Some(domain) =
            solve_linear_domain_for_cell(&linear, cell, coefficient, values, field_modulus)
        else {
            continue;
        };

        inferences.push((cell.clone(), domain));
    }

    inferences
}

// A Base-Conv alakból előre irányú domainkövetkeztetést végez: y0 + c*y1 + ... + c^n*yn - x = 0 mellett
// a yi in [0,c-1] korlátokból x-re a [0,c^(n+1)-1] lefedő halmazt állítja elő.
// Intervallumot nem tárol, ezért csak reprezentálható méretű teljes véges halmazt képez.
//Ez nem állítja, hogy a csomagolt domain minden eleme megvalósítható a többi kényszer mellett.
pub(super) fn infer_base_conv_value_domains(
    expr: &UcpExpr,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Vec<(CellId, UcpValueDomain)> {
    let Some(linear) = linearize(expr, values) else {
        return Vec::new();
    };

    if linear.constant != BigInt::from(0) {
        return Vec::new();
    }

    let mut inferences = Vec::new();

    for (target, target_coefficient) in &linear.terms {
        if !is_plus_or_minus_one(target_coefficient) || values.domain_is_complete(target) {
            continue;
        }

        let Some(domain) = infer_base_conv_value_domain_for_target(
            &linear,
            target,
            target_coefficient,
            values,
            field_modulus,
        ) else {
            continue;
        };

        push_domain_inference(&mut inferences, target.clone(), domain);
    }

    inferences
}

// A csomagolt célcellához felismeri az 1,c,c^2,... együtthatómintát.
fn infer_base_conv_value_domain_for_target(
    linear: &LinearExpr,
    target: &CellId,
    target_coefficient: &BigInt,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Option<UcpValueDomain> {
    let mut digits_with_coefficients = Vec::new();

    for (cell, coefficient) in &linear.terms {
        if cell == target {
            continue;
        }

        let digit_coefficient = -coefficient * target_coefficient;
        if digit_coefficient <= BigInt::from(0) {
            return None;
        }

        digits_with_coefficients.push((cell.clone(), digit_coefficient));
    }

    let (base, digits) = parse_base_conv_digit_powers(digits_with_coefficients)?;
    let max_digit = &base - BigInt::from(1);

    if digits
        .iter()
        .any(|digit| !values.domain_is_subset_of_range(digit, &BigInt::from(0), &max_digit))
    {
        return None;
    }

    let domain_size = pow_bigint(&base, digits.len());
    if domain_size <= BigInt::from(0) || domain_size > BigInt::from(MAX_FINITE_DOMAIN_SIZE as i64) {
        return None;
    }

    let mut domain_values = Vec::new();
    let mut value = BigInt::from(0);
    while value < domain_size {
        domain_values.push(value.clone());
        value += 1;
    }

    finite_domain_from_values(domain_values, field_modulus)
}

// A Base-Conv felismeréséhez ellenőrzi az egymást követő c-hatványokat.
fn parse_base_conv_digit_powers(
    mut digits_with_coefficients: Vec<(CellId, BigInt)>,
) -> Option<(BigInt, Vec<CellId>)> {
    if digits_with_coefficients.len() < 2 {
        return None;
    }

    digits_with_coefficients.sort_by(|left, right| left.1.cmp(&right.1).then(left.0.cmp(&right.0)));

    if digits_with_coefficients[0].1 != BigInt::from(1) {
        return None;
    }

    let base = digits_with_coefficients[1].1.clone();
    if base <= BigInt::from(1) {
        return None;
    }

    let mut expected = BigInt::from(1);
    let mut digits = Vec::with_capacity(digits_with_coefficients.len());

    for (digit, coefficient) in digits_with_coefficients {
        if coefficient != expected {
            return None;
        }

        digits.push(digit);
        expected *= &base;
    }

    Some((base, digits))
}

fn pow_bigint(base: &BigInt, exponent: usize) -> BigInt {
    let mut result = BigInt::from(1);
    for _ in 0..exponent {
        result *= base;
    }
    result
}

fn is_plus_or_minus_one(value: &BigInt) -> bool {
    value == &BigInt::from(1) || value == &BigInt::from(-1)
}

// A célcella domainjét nulla jobb oldalú lineáris egyenletből számítja.
fn solve_linear_domain_for_cell(
    linear: &LinearExpr,
    target: &CellId,
    coefficient: &BigInt,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Option<UcpValueDomain> {
    solve_linear_domain_for_cell_with_rhs(
        linear,
        target,
        coefficient,
        &UcpValueDomain::exact(BigInt::from(0)),
        values,
        field_modulus,
    )
}

// A célcella domainjét tetszőleges véges jobb oldali halmazból számítja.
//a*x + rest = rhs alapján az (rhs-rest)/a értékeket gyűjti, a többi cella domainjeiből.
fn solve_linear_domain_for_cell_with_rhs(
    linear: &LinearExpr,
    target: &CellId,
    coefficient: &BigInt,
    rhs_domain: &UcpValueDomain,
    values: &UcpValueFacts,
    field_modulus: Option<&BigInt>,
) -> Option<UcpValueDomain> {
    let mut rest_values = vec![normalize_value(linear.constant.clone(), field_modulus)?];

    for (cell, term_coefficient) in &linear.terms {
        if cell == target {
            continue;
        }

        let domain = values.domain(cell)?;
        let term_values = domain_values(domain);

        if rest_values.len().saturating_mul(term_values.len()) > MAX_FINITE_DOMAIN_SIZE {
            return None;
        }

        let mut next_values = Vec::with_capacity(rest_values.len() * term_values.len());
        for rest in &rest_values {
            for value in &term_values {
                next_values.push(normalize_value(
                    rest + term_coefficient * value,
                    field_modulus,
                )?);
            }
        }
        rest_values = next_values;
    }

    let rhs_values = domain_values(rhs_domain);
    if rhs_values.len().saturating_mul(rest_values.len()) > MAX_FINITE_DOMAIN_SIZE {
        return None;
    }

    let mut solved_values = Vec::with_capacity(rhs_values.len() * rest_values.len());
    // Az együttható minden jelöltnél azonos, ezért az inverzét csak egyszer számítja ki.
    let inverse = match field_modulus {
        Some(modulus) => Some(mod_inverse(coefficient, modulus)?),
        None => None,
    };
    for rhs in &rhs_values {
        for rest in &rest_values {
            let value = match &inverse {
                Some(inverse) => normalize_value((rhs - rest) * inverse, field_modulus)?,
                None => solve_linear_value(&(rhs - rest), coefficient, None)?,
            };
            solved_values.push(value);
        }
    }

    finite_domain_from_values(solved_values, field_modulus)
}

// Testben moduláris inverzzel oszt; modulus nélkül csak maradék nélküli egész osztást fogad el.
fn solve_linear_value(
    numerator: &BigInt,
    coefficient: &BigInt,
    field_modulus: Option<&BigInt>,
) -> Option<BigInt> {
    match field_modulus {
        Some(modulus) => {
            if modulus <= &BigInt::from(1) {
                return None;
            }
            let inverse = mod_inverse(coefficient, modulus)?;
            normalize_value(numerator * inverse, Some(modulus))
        }
        None => {
            if coefficient == &BigInt::from(0) {
                return None;
            }
            if numerator % coefficient != BigInt::from(0) {
                return None;
            }
            bounded_value(numerator / coefficient)
        }
    }
}

#[cfg(test)]
mod division_regression_tests {
    use super::*;

    #[test]
    fn batched_domain_division_matches_exhaustive_field_arithmetic() {
        let x = CellId::advice(0, 0);
        let y = CellId::advice(1, 0);
        for prime_or_composite in [17i64, 21, 97] {
            let modulus = BigInt::from(prime_or_composite);
            for coefficient in 0..prime_or_composite {
                let expression = UcpExpr::add(
                    UcpExpr::scale_by(
                        UcpExpr::var(x.clone()),
                        super::super::UcpScalar::known_i64(coefficient),
                    ),
                    UcpExpr::neg(UcpExpr::var(y.clone())),
                );
                let mut values = UcpValueFacts::new();
                values.mark_domain(
                    y.clone(),
                    UcpValueDomain::finite_set([1.into(), 3.into(), 5.into()]).unwrap(),
                );
                let inferred = infer_value_domains_from_zero_equation_with_modulus(
                    &expression,
                    &values,
                    &modulus,
                )
                .into_iter()
                .find(|(cell, _)| cell == &x)
                .map(|(_, domain)| domain);
                let invertible = (1..prime_or_composite)
                    .any(|inverse| coefficient * inverse % prime_or_composite == 1);
                let expected = if invertible {
                    UcpValueDomain::finite_set(
                        (0..prime_or_composite)
                            .filter(|value| {
                                [1, 3, 5].contains(&(coefficient * value % prime_or_composite))
                            })
                            .map(|value| normalize_field_value(value.into(), &modulus).unwrap()),
                    )
                } else {
                    None
                };
                assert_eq!(
                    inferred, expected,
                    "modulus={prime_or_composite} coefficient={coefficient}"
                );
            }
        }
    }
}

//Kiterjesztett euklideszi algoritmus; csak gcd(value, modulus)=1 esetén létezik inverz.
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

// Belső 0..p-1 reprezentánst számít; a Delta előjeles alakját külön segédfüggvény készíti.
pub(super) fn mod_field(value: BigInt, modulus: &BigInt) -> BigInt {
    let mut value = value % modulus;
    if value < BigInt::from(0) {
        value += modulus;
    }
    value
}

// UcpExpr-ből konstans + együttható * cella + ... lineáris alakot készít.
//Konkrétan ismert részeket behelyettesít; az egyértelműség önmagában nem ad numerikus együtthatót.
fn linearize(expr: &UcpExpr, values: &UcpValueFacts) -> Option<LinearExpr> {
    if let Some(value) = evaluate_expr(expr, values) {
        return Some(LinearExpr::constant(value));
    }

    match expr {
        UcpExpr::Var(cell) => Some(LinearExpr::term(cell.clone(), BigInt::from(1))),
        UcpExpr::Const(_) => None,
        UcpExpr::Neg(inner) => {
            linearize(inner, values).map(|linear| linear.scale(BigInt::from(-1)))
        }
        UcpExpr::Add(left, right) => Some(linearize(left, values)?.add(linearize(right, values)?)),
        UcpExpr::Mul(left, right) => {
            if let Some(value) = evaluate_expr(left, values) {
                return Some(linearize(right, values)?.scale(value));
            }
            if let Some(value) = evaluate_expr(right, values) {
                return Some(linearize(left, values)?.scale(value));
            }
            None
        }
        UcpExpr::Scale(inner, scalar) => match scalar {
            UcpScalar::Zero => Some(LinearExpr::constant(BigInt::from(0))),
            UcpScalar::Known(scale) => {
                Some(linearize(inner, values)?.scale(bounded_value(scale.clone())?))
            }
            UcpScalar::NonZero | UcpScalar::Unknown => None,
        },
    }
}

// A belső lineáris alak konstans-, változó-, összeg- és skálázási műveleteit biztosítja.
impl LinearExpr {
    //Konstans lineáris kifejezést hoz létre
    fn constant(value: BigInt) -> Self {
        Self {
            constant: value,
            terms: HashMap::new(),
        }
    }

    //Egy darab cellatagot hoz létre a megadott együtthatóval
    fn term(cell: CellId, coefficient: BigInt) -> Self {
        Self {
            constant: BigInt::from(0),
            terms: HashMap::from([(cell, coefficient)]),
        }
    }

    //Két lineáris kifejezést összead, az azonos cellák együtthatóit összevonva
    fn add(mut self, other: Self) -> Self {
        self.constant += other.constant;
        for (cell, coefficient) in other.terms {
            let entry = self.terms.entry(cell).or_insert_with(|| BigInt::from(0));
            *entry += coefficient;
        }
        self.terms
            .retain(|_, coefficient| coefficient != &BigInt::from(0));
        self
    }

    //Lineáris kifejezést beszoroz egy skalárral
    fn scale(mut self, scalar: BigInt) -> Self {
        self.constant *= &scalar;
        for coefficient in self.terms.values_mut() {
            *coefficient *= &scalar;
        }
        self.terms
            .retain(|_, coefficient| coefficient != &BigInt::from(0));
        self
    }
}
