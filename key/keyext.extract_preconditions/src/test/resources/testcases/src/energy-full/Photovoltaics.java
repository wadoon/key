
public class Photovoltaics extends EnergyProducer {
    
    /* Modes 0 -- 4 represent the maximum solar irradiance which can be handled.
     */
    
    /*@ public normal_behavior
      @ requires 0 <= mode && mode <= 4;
      @ ensures this.mode == mode;
      @ assignable this.mode;
      @*/
    public Photovoltaics(int mode) {
        this.mode = mode;
    }

    public void run(Capacitor c, EnvironmentSensor s) {
        if (s.getSunIrradiance() > mode) {
            c.addCharge(mode / 2);
        } else {
            c.addCharge(s.getSunIrradiance() / 2);
        }
    }
}
