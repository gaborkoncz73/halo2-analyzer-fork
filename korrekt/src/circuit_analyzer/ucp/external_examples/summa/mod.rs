//! A Summa Solvency v2 egyenlegkapcsolasanak vizsgalata; az eredetet a README rogziti.

#[allow(dead_code, unused_imports, unused_variables)]
mod upstream {
    pub mod entry;
    pub mod operation_helpers;
    pub mod range_check;
    pub mod range_utils;
    pub mod univariate_grand_sum;
}

mod tests;
