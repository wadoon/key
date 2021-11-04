
public final class EnvironmentSensor {

    private /*@spec_public@*/ int windSpeed;
    private /*@spec_public@*/ int sunIrradiance;

    /*@ public normal_behavior
      @ ensures_free this.sunIrradiance>0;
      @ ensures_free this.windSpeed>0;
      @ assignable this.*;
      @*/
    public EnvironmentSensor();
    
    /*@ public normal_behavior
      @ ensures \result == this.windSpeed;
      @ ensures_free \result >= 0;
      @ assignable \strictly_nothing;
      @*/ 
    public int getWindSpeed() {
        return windSpeed;
    }

    /*@ public normal_behavior
      @ ensures \result == this.sunIrradiance;
      @ ensures_free \result >= 0;
      @ assignable \strictly_nothing;
      @*/ 
    public int getSunIrradiance() {
        return sunIrradiance;
    }
    
    /*@ public normal_behavior
      @ ensures_free this.windSpeed >= 0;
      @ ensures_free this.sunIrradiance >= 0;
      @ assignable this.*;
      @*/ 
    public void updateValues();
}
