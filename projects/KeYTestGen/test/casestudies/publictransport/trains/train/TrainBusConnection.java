package casestudies.publictransport.trains.train;

import casestudies.publictransport.buses.admin.Company;
import casestudies.publictransport.buses.travel.Driver;
import casestudies.publictransport.buses.travel.Route;
import casestudies.publictransport.buses.vehicle.Bus;

public class TrainBusConnection {
    Train t;
    Bus b;

    /*@ public invariant null == b <==> t == null; @ */
    protected TrainBusConnection(String str) {

    }

    /*@ public normal_behavior 
     *@ ensures \old(t) != null ==> 
                   (b.getCompany() == company && 
                   b.getDriver() == driver && 
                   b.getRoute() == route);
     
     *@ensures \old(t) == null ==> t == null;
     */
    public void initialize(Train t, Company company, Driver driver, Route route) {
        if (t == null || b == null) {
            return;
        } else {
            this.t = t;
            this.b = new Bus(company, driver, route);
        }
    }
}