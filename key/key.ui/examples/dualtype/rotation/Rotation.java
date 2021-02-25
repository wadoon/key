package benchmarks.rotation;

public class Rotation {

    final static double cos90 = 6.123233995736766E-17;
    final static double sin90 = 1.0;

    // rotates a 2D vector by 90 degrees
    public static double[] rotate(double[] vec) {

        double degree = Math.toRadians(90.0);
        // double x = vec[0] * cos90 - vec[1] * sin90;
        double x = vec[0] * Math.cos(degree) - vec[1] * Math.sin(degree);

        // double y = vec[0] * sin90 + vec[1] * cos90;
        double y = vec[0] * Math.sin(degree) + vec[1] * Math.cos(degree);
        return new double[]{x, y};
    }

    /*@
      @ public normal_behaviour
      @  requires (\forall int i; 0 <= i && i < vec.length;
      @   vec[i] > 1.0r && vec[i] < 2.0r) && vec.length == 2;
      @  ensures  \fp_err(\result[0]) < 0.000000000000001r && \fp_err(\result[1]) < 0.000000000000001r;
      @*/
    public static double[] computeError(double[] vec) {

        double[] temp = rotate(rotate(rotate(rotate(vec))));
        // return new double[]{Math.abs(temp[0] - vec[0]), Math.abs(temp[1] - vec[1])};
        return temp;
    }

    /*@
      @ public normal_behaviour
      @  requires (\forall int i; 0 <= i && i < vec.length;
      @   vec[i] > 1.0r && vec[i] < 2.0r) && vec.length == 2;
      @  ensures \fp_err(\result[0]) < 0.000000000000001r && \fp_err(\result[1]) < 0.000000000000001r;
      @*/
    public static double[] computeRelErr(double[] vec) {

        double[] temp = rotate(rotate(rotate(rotate(vec))));
        // return new double[]{Math.abs(temp[0] - vec[0]) / vec[0], Math.abs(temp[1] - vec[1]) / vec[1]}
        return temp;
    }
}
