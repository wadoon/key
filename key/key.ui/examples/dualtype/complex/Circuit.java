//Analysis of RL circuit
public class Circuit {

    double maxVoltage;
    double frequency;
    double resistance;
    double inductance;

    /*@ public normal_behaviour
      @ requires  this.frequency > 1.0 && this.frequency < 100.0 && this.resistance > 1.0  && this.resistance < 50.0 &&
      @  this.inductance > 0.001 && this.inductance < 0.004;
      @ ensures \fp_nice(\result.imaginaryPart) && \result.imaginaryPart < 10.0 && \result.imaginaryPart > 0.0001;
      @ also
      @ requires  this.frequency > 1.0r && this.frequency < 100.0r && this.resistance > 1.0r  && this.resistance < 50.0r &&
      @  this.inductance > 0.001r && this.inductance < 0.004r;
      @ ensures \fp_err(\result.imaginaryPart) < 0.000000000000001r && \result.imaginaryPart < 10.0r && \result.imaginaryPart > 0.000r;
      @*/
    public Complex computeImpedance() {

        return new Complex(resistance, 2.0 * Math.PI * frequency * inductance);
    }

    /*@ public normal_behaviour
      @ requires this.maxVoltage > 1.0  && this.maxVoltage < 12.0 && this.frequency > 1.0 && this.frequency < 100.0 &&
      @  this.resistance > 1.0  && this.resistance < 50.0 && this.inductance > 0.001 &&
      @  this.inductance < 0.004;
      @ ensures \fp_nice(\result.realPart) && \fp_nice(\result.imaginaryPart);
      @ also
      @ requires this.maxVoltage > 1.0r  && this.maxVoltage < 12.0r && this.frequency > 1.0r && this.frequency < 100.0r &&
      @  this.resistance > 1.0r  && this.resistance < 50.0r && this.inductance > 0.001r &&
      @  this.inductance < 0.004r;
      @ ensures \fp_err(\result.realPart) < 0.000000000000001r && \fp_err(\result.imaginaryPart) < 0.000000000000001r;
      @*/
    public Complex ComputeCurrent() {

        return new Complex(maxVoltage, 0.0).divide(computeImpedance());
    }

    //computes instantaneous current
  /*@ public normal_behaviour
    @ requires this.maxVoltage > 1.0  && this.maxVoltage < 12.0 && this.frequency > 1.0 && this.frequency < 100.0 &&
    @  this.resistance > 1.0  && this.resistance < 50.0 && this.inductance > 0.001 &&
    @  this.inductance < 0.004 && time > 0.0 && time < 300.0;
    @ ensures \fp_nice(\result);
    @ also
    @ requires this.maxVoltage > 1.0r  && this.maxVoltage < 12.0r && this.frequency > 1.0r && this.frequency < 100.0r &&
    @  this.resistance > 1.0r  && this.resistance < 50.0r && this.inductance > 0.001r &&
    @  this.inductance < 0.004r && time > 0.0r && time < 300.0r;
    @ ensures \fp_err(\result) < 0.000000000000001r;
    @*/
    public double computeInstantCurrent(double time) {

        Complex current = ComputeCurrent();
        double maxCurrent = Math.sqrt(current.getRealPart() * current.getRealPart() + current.getImaginaryPart() * current.getImaginaryPart());
        double theta = Math.atan(current.getImaginaryPart() / current.getRealPart());

        return maxCurrent * Math.cos((2.0 * Math.PI * frequency * time) + theta);
    }

    //computes instantaneous voltage
  /*@ public normal_behaviour
    @ requires this.maxVoltage > 1.0  && this.maxVoltage < 12.0 && this.frequency > 1.0 &&
    @  this.frequency < 100.0 && time > 0.0 && time < 300.0;
    @ ensures \fp_nice(\result);
    @ also
    @ requires this.maxVoltage > 1.0r  && this.maxVoltage < 12.0r && this.frequency > 1.0r &&
    @  this.frequency < 100.0r && time > 0.0r && time < 300.0r;
    @ ensures \fp_err(\result) < 0.000000000000001r;
    @*/
    public double computeInstantVoltage(double time) {

        return maxVoltage * Math.cos(2.0 * Math.PI * frequency * time);
    }
}
