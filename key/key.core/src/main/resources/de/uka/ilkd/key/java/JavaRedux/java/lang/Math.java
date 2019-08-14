package java.lang;

public class Math {

    public static final double PI = 3.14159265358979323846;

    public static double toRadians(double angdeg) {
        return angdeg / 180.0 * PI;
    }
    public static double toDegrees(double angrad) {
        return angrad * 180.0 / PI;
    }
    public static double abs(double d) {
        return (d <= 0) ? 0 - d : d;
    }
    public static double max(double a, double b) {
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



}
