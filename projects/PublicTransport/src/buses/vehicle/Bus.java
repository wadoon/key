package buses.vehicle;

import buses.admin.Company;
import buses.admin.Nationality;
import buses.travel.Driver;
import buses.travel.Route;

public class Bus {
  private Company company;
  private Nationality nationality;
  private Driver driver;
  private Route route;
  
  	public Bus(String company, String driver, Route route){
  		this.company = new Company(company);
  		this.driver = new Driver(driver);
  		this.route = route;
  	}
  	
  	public Bus(Company company, Driver driver, Route route){
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
	
	public Nationality getNationality() {
		return nationality;
	}
	
	public Route getRoute() {
		return route;
	}
	
	/*
	 * Setters
	 */
	public void setNationality(Nationality nationality) {
		this.nationality = nationality;
	}

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
