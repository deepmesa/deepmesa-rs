use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::MatrixType;

macro_rules! dim_assert_matrix {
    ($m:ident, $rows:literal, $cols:literal, $data_len:literal, $transpose:literal, $square:literal, $simd_optimized:literal) => {
        assert_eq!($m.rows, $rows);
        assert_eq!($m.cols, $cols);
        assert_eq!($m.len, $data_len);
        assert_eq!($m.is_transpose, $transpose);
        assert_eq!($m.is_square, $square);
        assert_eq!($m.is_simd_optimized(), $simd_optimized);
        assert_eq!($m.matrix_type(), MatrixType::DualIndex);
    };
}

macro_rules! dim_test_new {
    ($fn_name:ident,
     $t:ty,
     $rows:literal,
     $cols:literal,
     $data_len:literal) => {
        #[test]
        fn $fn_name() {
            let m: Matrix<$t> = Matrix::new($rows, $cols, MatrixType::DualIndex, false);
            dim_assert_matrix!(m, $rows, $cols, $data_len, false, false, false);
        }
    };
}

dim_test_new!(test_new_f32, f32, 3, 2, 6);
dim_test_new!(test_new_f64, f64, 3, 2, 6);
dim_test_new!(test_new_u8, u8, 3, 2, 6);
dim_test_new!(test_new_u16, u16, 3, 2, 6);
dim_test_new!(test_new_u32, u32, 3, 2, 6);
dim_test_new!(test_new_u64, u64, 3, 2, 6);
dim_test_new!(test_new_u128, u128, 3, 2, 6);
dim_test_new!(test_new_i8, i8, 3, 2, 6);
dim_test_new!(test_new_i16, i16, 3, 2, 6);
dim_test_new!(test_new_i32, i32, 3, 2, 6);
dim_test_new!(test_new_i64, i64, 3, 2, 6);
dim_test_new!(test_new_i128, i128, 3, 2, 6);

macro_rules! dim_test_new_square {
    ($fn_name:ident,
     $t:ty,
     $rows:literal,
     $cols:literal,
     $data_len:literal) => {
        #[test]
        fn $fn_name() {
            let m: Matrix<$t> = Matrix::new($rows, $cols, MatrixType::DualIndex, false);
            dim_assert_matrix!(m, $rows, $cols, $data_len, false, true, false);
        }
    };
}

dim_test_new_square!(test_new_square_f32, f32, 3, 3, 9);
dim_test_new_square!(test_new_square_f64, f64, 3, 3, 9);
dim_test_new_square!(test_new_square_u8, u8, 3, 3, 9);
dim_test_new_square!(test_new_square_u16, u16, 3, 3, 9);
dim_test_new_square!(test_new_square_u32, u32, 3, 3, 9);
dim_test_new_square!(test_new_square_u64, u64, 3, 3, 9);
dim_test_new_square!(test_new_square_u128, u128, 3, 3, 9);
dim_test_new_square!(test_new_square_i8, i8, 3, 3, 9);
dim_test_new_square!(test_new_square_i16, i16, 3, 3, 9);
dim_test_new_square!(test_new_square_i32, i32, 3, 3, 9);
dim_test_new_square!(test_new_square_i64, i64, 3, 3, 9);
dim_test_new_square!(test_new_square_i128, i128, 3, 3, 9);

macro_rules! dim_test_new_so {
    ($fn_name:ident,
     $t:ty,
     $rows:literal,
     $cols:literal,
     $data_len:literal) => {
        #[test]
        fn $fn_name() {
            let m: Matrix<$t> = Matrix::new($rows, $cols, MatrixType::DualIndex, true);
            dim_assert_matrix!(m, $rows, $cols, $data_len, false, false, true);
        }
    };
}

dim_test_new_so!(test_new_so_f32, f32, 3, 2, 6);
dim_test_new_so!(test_new_so_f64, f64, 3, 2, 6);
dim_test_new_so!(test_new_so_u8, u8, 3, 2, 6);
dim_test_new_so!(test_new_so_u16, u16, 3, 2, 6);
dim_test_new_so!(test_new_so_u32, u32, 3, 2, 6);
dim_test_new_so!(test_new_so_u64, u64, 3, 2, 6);
dim_test_new_so!(test_new_so_u128, u128, 3, 2, 6);
dim_test_new_so!(test_new_so_i8, i8, 3, 2, 6);
dim_test_new_so!(test_new_so_i16, i16, 3, 2, 6);
dim_test_new_so!(test_new_so_i32, i32, 3, 2, 6);
dim_test_new_so!(test_new_so_i64, i64, 3, 2, 6);
dim_test_new_so!(test_new_so_i128, i128, 3, 2, 6);

macro_rules! dim_test_new_square_so {
    ($fn_name:ident,
     $t:ty,
     $rows:literal,
     $cols:literal,
     $data_len:literal) => {
        #[test]
        fn $fn_name() {
            let m: Matrix<$t> = Matrix::new($rows, $cols, MatrixType::DualIndex, true);
            dim_assert_matrix!(m, $rows, $cols, $data_len, false, true, true);
        }
    };
}

dim_test_new_square_so!(test_new_square_so_f32, f32, 3, 3, 9);
dim_test_new_square_so!(test_new_square_so_f64, f64, 3, 3, 9);
dim_test_new_square_so!(test_new_square_so_u8, u8, 3, 3, 9);
dim_test_new_square_so!(test_square_so_new_u16, u16, 3, 3, 9);
dim_test_new_square_so!(test_square_so_new_u32, u32, 3, 3, 9);
dim_test_new_square_so!(test_square_so_new_u64, u64, 3, 3, 9);
dim_test_new_square_so!(test_square_so_test_new_u128, u128, 3, 3, 9);
dim_test_new_square_so!(test_square_so_test_new_i8, i8, 3, 3, 9);
dim_test_new_square_so!(test_square_so_test_new_i16, i16, 3, 3, 9);
dim_test_new_square_so!(test_square_so_test_new_i32, i32, 3, 3, 9);
dim_test_new_square_so!(test_square_so_test_new_i64, i64, 3, 3, 9);
dim_test_new_square_so!(test_square_so_test_new_i128, i128, 3, 3, 9);
