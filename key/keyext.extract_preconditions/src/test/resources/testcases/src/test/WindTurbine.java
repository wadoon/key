/**
 * According to [1] windturbines have a survival speed around 40 to 72 m/s
 *
 * [1] https://en.wikipedia.org/wiki/Wind_turbine_design
 */
class WindTurbine {
    /**
     * Speed of the windturbine in m/s
     */
    private /*@ spec_public @*/ int currentSpeed;

    public WindTurbine() {
        this.currentSpeed = 0;
    }

    /*@ public normal_behavior
      @ ensures currentSpeed == \old(currentSpeed)+1;
      @ ensures currentSpeed >= 72 ==> !\result;
     */
    public boolean incSpeedAndCheckSurvival() {
        return (currentSpeed++ < 72);
    }
}