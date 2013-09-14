package buses.vehicle;

import buses.admin.Company;
import buses.admin.Nationality;
import buses.travel.Driver;
import buses.travel.Route;

/**
 * Represents a bus used in a public transportation system.
 * 
 * @author christopher
 */
public class Bus {

    /**
     * The company which operates the bus.
     */
    private Company company;

    /**
     * The driver of the bus.
     */
    private Driver driver;

    /**
     * The route covered by the bus.
     */
    private Route route;

    public Bus(Company company, Driver driver, Route route) {
        this.company = company;
        this.driver = driver;
        this.route = route;
    }

    /*
     * Getters
     */
    public Company getCompany() {
        return company;
    }

    public Driver getDriver() {
        return driver;
    }

    public Route getRoute() {
        return route;
    }

    /*
     * Setters
     */
    public void setDriver(Driver driver) {
        this.driver = driver;
    }

    public void setRoute(Route route) {
        this.route = route;
    }

    public void setCompany(Company company) {
        this.company = company;
    }
}