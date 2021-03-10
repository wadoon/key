package java.lang;

public class Math {

    public static final double PI = 3.14159265358979323846;
    public static final double E = 2.7182818284590452354;


    public static double abs(double a) {
        return (a <= 0.0D) ? 0.0D - a : a;
    }

    public static float abs(float a) {
        return (a <= 0.0F) ? 0.0F - a : a;
    }

    public static double acos(double d);

    public static double asin(double d);

    public static double atan(double a);

    public static double atan2(double a, double b);

    public static double cbrt(double a);

    public static double cos(double d);

    public static double cosh(double x);

    public static double exp(double a);

    public static double expm1(double x);

    public static double hypot(double x, double y);

    public static double log(double a);

    public static double log10(double a);

    public static double log1p(double x);

    public static double max(double a, double b) {
        if (a != a)
            return a;
        return (a >= b) ? a : b;
    }

    public static float max(float a, float b) {
        if (a != a)
            return a;
        return (a >= b) ? a : b;
    }

    public static double pow(double a, double b);

    public static double sin(double d);

    public static double sinh(double x);

    public static double sqrt(double d);

    public static double tan(double d);

    public static double tanh(double d);

    public static double toDegrees(double angrad) {
        return angrad * 180.0 / PI;
    }

    public static double toRadians(double angdeg) {
        return angdeg / 180.0 * PI;
    }

}
