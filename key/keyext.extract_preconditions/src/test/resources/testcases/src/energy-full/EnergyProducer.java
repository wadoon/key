
public abstract class EnergyProducer {
    
    /*
     * What the modes mean depends on the subclass.
     */

    //@ public invariant 0 <= mode && mode <= 4;
    
    protected /*@spec_public@*/ int mode;

    /*@ public normal_behavior
      @ requires \invariant_for(c);
      @// requires c.mode < 3; // for GasTurbine
      @// requires this.mode >= s.windSpeed; // for WindTurbine
      @// requires c.mode < 4 - s.windSpeed; // for WindTurbine
      @// requires c.mode < 4 - s.sunIrradiance || c.mode < 4 - this.mode && s.sunIrradiance > this.mode; // for Photovoltaics
      @ ensures \invariant_for(c);
      @ assignable c.mode, this.mode;
      @*/
    public abstract void run(Capacitor c, EnvironmentSensor s);
    
    /*@ public normal_behavior
      @ ensures \result == this.mode;
      @ assignable \strictly_nothing;
      @*/ 
    public int getMode() {
        return mode;
    }
}
