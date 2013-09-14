package targetmodels.publictransport.trains.train;

public class Station {

    /**
     * The central hub of the train network.
     */
    public static final Station CENTRAL = new Station("CENTRAL");

    /**
     * The name of the station.
     */
    private String name;

    /**
     * @param str
     *            name of the station
     * @return the a new station
     */
    public Station(String str) {
        name = str;
    }

    /*@ public normal_behavior
     *@ requires t != null && w != null;
     *@ ensures t.hasWagon(w);
     */
    public void addWagon(Train t, Wagon w) {
        t.addWagon(w);
    }
}