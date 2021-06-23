/**
 * According to [1] windturbines have a survival speed around 40 to 72 m/s
 *
 * [1] https://en.wikipedia.org/wiki/Wind_turbine_design
 */
class WindTurbine2 {
    /**
     * Speed of the windturbine in m/s
     */
    private /*@ spec_public @*/ int currentSpeed;

    public WindTurbine2() {
        this.currentSpeed = 0;
    }

    /*@ public normal_behavior
      @ requires inc > 0 && inc < 5;
      @ requires currentSpeed < 72;
      @ ensures currentSpeed == \old(currentSpeed)+inc;
      @ ensures \old(currentSpeed)+inc >= 72 ==> !\result;
     */
    public boolean incSpeedAndCheckSurvival(int inc) {
        if (this.currentSpeed>72) {
            return false;
        } else {
            this.currentSpeed+=inc;
            return true;
        }
    }
}