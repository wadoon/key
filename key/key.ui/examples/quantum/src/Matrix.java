public class Matrix {

    protected final int rows;
    protected final int cols;

    protected final Complex[][] content;

    public Matrix(int rows, int cols) {
        this.rows = rows;
        this.cols = cols;
        this.content = new Complex[rows][cols];
    }

    public Matrix(int rows, int cols, Complex[][] content) {
        this.rows = rows;
        this.cols = cols;
        this.content = content;
    }

    public static Complex[][] kProd(Complex[][] a, Complex[][] b) {
        final int aRows = a.length;
        final int aCols = aRows > 0 ? a[0].length : 0;
        final int bRows = b.length;
        final int bCols = bRows > 0 ? b[0].length : 0;
        final Complex[][] result = new Complex[aRows * bRows][];

        for (int i = 0; i < result.length; i++) {
            result[i] = new Complex[aCols * bCols];
        }
        for (int aRow = 0; aRow < aRows; aRow++) {
            for (int aCol = 0; aCol < aCols; aCol++) {
                for (int bRow = 0; bRow < bRows; bRow++) {
                    for (int bCol = 0; bCol < bCols; bCol++) {
                        final int cRow = aRow * bRows + bRow;
                        final int cCol = aCol * bCols + bCol;
                        result[cRow][cCol] = Complex.mul(a[aRow][aCol], b[bRow][bCol]);
                    }
                }
            }
        }
        return result;
    }


    public static Matrix kProd(Matrix a, Matrix b) {
        Matrix[][] product = Matrix.kProd(a.content, b.content);
        return new Matrix(product.length, product.length > 0 ? product[0].length : 0);
    }

    public static Complex[][] mProd(Complex[][] a, Complex[][] b) {
        final int aRows = a.length;
        final int aCols = aRows > 0 ? a[0].length : 0;
        final int bRows = b.length;
        final int bCols = bRows > 0 ? b[0].length : 0;

        final Complex[][] result = new Complex[aRows][bCols];

        for (int i = 0; i < aRows; i++) {
            for (int j = 0; j < bCols; j++) {
                for (int m = 0; m<aCols; m++) {
                    for (int n = 0; n<bRows; n++) {
                        result[i][j] = Complex.mul(a[i][m], b[n][j]);
                    }
                }
            }
        }
        return result;
    }

    public static Matrix mProd(Matrix a, Matrix b) {
        return new Matrix(a.rows, b.cols, mProd(a.content, b.content));
    }

    public static Matrix sProd(Matrix a, Matrix b) {
        throw new RuntimeException();
    }
}
