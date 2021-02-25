public class Complex {

    double realPart;
    double imaginaryPart;

    public Complex(double realPart, double imaginaryPart) {

        this.realPart = realPart;
        this.imaginaryPart = imaginaryPart;
    }

    public void add(Complex c) {

        this.realPart = this.realPart + c.realPart;
        this.imaginaryPart = this.imaginaryPart + c.imaginaryPart;
    }

    public Complex divide(Complex c) {

        double denominator = (c.realPart * c.realPart) + (c.imaginaryPart * c.imaginaryPart);
        this.realPart = ((this.realPart * c.realPart) + (this.imaginaryPart * c.imaginaryPart)) / denominator;
        this.imaginaryPart = ((this.imaginaryPart * c.realPart) - (this.realPart * c.imaginaryPart)) / denominator;

        return this;
    }

    public double compare(Complex c) {

        if (this.realPart == c.realPart)
            return this.imaginaryPart - c.imaginaryPart;

        else return this.realPart - c.realPart;
    }

    public Complex reciprocal() {

        double scale = realPart * realPart + imaginaryPart * imaginaryPart;

        return new Complex(realPart / scale, -imaginaryPart / scale);
    }

    public double getRealPart() {
        return realPart;
    }

    public double getImaginaryPart() {
        return imaginaryPart;
    }
}

