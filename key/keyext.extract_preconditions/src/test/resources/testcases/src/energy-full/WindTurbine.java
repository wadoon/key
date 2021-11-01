
public final class WindTurbine extends EnergyProducer {
    
    /* Modes 0 -- 4 represent the maximum wind speed which can be handled.
     */
    
    /*@ public normal_behavior
      @ requires 0 <= mode && mode <= 4;
      @ ensures this.mode == mode;
      @ assignable this.*;
      @*/
    public WindTurbine(int mode) {
        this.mode = mode;
    }

    public void run(Capacitor c, EnvironmentSensor s) {
        if (s.getWindSpeed() > mode) {
             throw new RuntimeException();
        }
        
        c.addCharge(s.getWindSpeed() / 2);
    }
}
