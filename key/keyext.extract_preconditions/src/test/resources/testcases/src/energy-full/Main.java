
public class Main {
    
    /*
     * This example includes several challenges for our approach:
     * 1. We need to first extract the error conditions for the inner methods
     *    (Capacitor::addCharge and EnergyProducer::run) and add them to their specifications
     *    before being able to extract the error condition for main1.
     * 2. The error conditions depend not only on the explicit arguments but also
     *    2.1. on fields of the explicit arguments, which should not be a problem
     *    2.2. on fields of the receiver argument, which are all contracted into a single field "mode"
     *    2.3. on the return values of called methods, which we need to deal with by either
     *         replacing these values with expressions that depend only on the input,
     *         or---if this is not possible---modeling parts of a method's behavior in Palladio.
     *         For an example of replacing the values, see the various getter methods. For an
     *         example where this isn't possible, see the fields of the EnvironmentSensor created
     *         in main1.
     *  3. Some of the services/methods have arguments with object types instead of primitive types.
     *     However, since the complete state of an object is its "mode," this should not be a problem.
     *     The exception is the EnvironmentSensor, which has two fields; if necessary these can also
     *     be easily simplified into a single "mode" field.
     */
    
    /*@ public normal_behavior
      @ requires 0 <= producerMode && producerMode <= 4;
      @ ensures true;
      @ assignable \everything;
      @*/   
    public final void main1(int producerType, int producerMode) {
        EnergyProducer producer;
        if (producerType == 0) {
            producer = new GasTurbine(producerMode);
        } else if (producerType == 1) {
            producer = new WindTurbine(producerMode);
        } else {
            producer = new Photovoltaics(producerMode);
        }
        
        Capacitor capacitor = new Capacitor();
        EnvironmentSensor sensor = new EnvironmentSensor();
        
        if (checkState(capacitor, producer, sensor, producerType)) {
            producer.run(capacitor, sensor);
        }
    }

    public final boolean checkState(Capacitor capacitor, EnergyProducer producer, EnvironmentSensor sensor, int producerType) {
        if (producerType==0) {
            return capacitor.getMode() <= 3;
        } else if (producerType==1) {
            WindTurbine windTurbine = (WindTurbine) producer;
            return capacitor.getMode() <= 4 - sensor.getWindSpeed() / 2
                    && sensor.getWindSpeed() < windTurbine.getMode();
        } else /*if (producer instanceof Photovoltaics)*/ {
            Photovoltaics pv = (Photovoltaics) producer;
            return capacitor.getMode() <= 4 - sensor.getSunIrradiance() / 2
                    || capacitor.getMode() <= 4 - pv.getMode() / 2 && sensor.getSunIrradiance() > pv.getMode();
        }
    }
}
