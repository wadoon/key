package java.lang;

public class Math {

    public static final double PI = 3.14159265358979323846;

    public static double toRadians(double angdeg) {
        return angdeg / 180.0 * PI;
    }
    public static double toDegrees(double angrad) {
        return angrad * 180.0 / PI;
    }
    public static double abs(double a) {
        return (a <= 0.0D) ? 0.0D - a : a;
    }
    public static float abs(float a) {
        return (a <= 0.0F) ? 0.0F - a : a;
    }
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
    public static double sin(double d);
    public static double asin(double d);
    public static double cos(double d);
    public static double acos(double d);
    public static double tan(double d);
    public static double atan2(double a, double b);
    public static double sqrt(double d);
    public static double pow(double a , double b);
    public static double exp(double a);
    public static double atan(double a);



}
