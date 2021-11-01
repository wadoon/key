
public final class GasTurbine extends EnergyProducer {
    
    /* Modes:
     * 0: fuel tank empty
     * 1: fuel tank almost empty
     * 2: fuel tank partially empty
     * 3: fuel tank almost full
     * 4: fuel tank full
     */
    
    /*@ public normal_behavior
      @ requires 0 <= mode && mode <= 4;
      @ ensures this.mode == mode;
      @ assignable this.*;
      @*/
    public GasTurbine(int mode) {
        this.mode = mode;
    }

    public void run(Capacitor c, EnvironmentSensor s) {
        if (mode > 0) {
            c.addCharge(1);
            --mode;
        }
    }
}
