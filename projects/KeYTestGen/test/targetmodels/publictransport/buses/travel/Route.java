package targetmodels.publictransport.buses.travel;

/**
 * Represents a transportation route between two points (intermediary stops are
 * not modelled for the sake of simplicity).
 * 
 * @author christopher
 */
public class Route {

    /**
     * The start location of the route.
     */
    String start;

    /**
     * The final location of the route.
     */
    String end;

    /**
     * @return the start location.
     */
    public String getStart() {
        return start;
    }

    /**
     * @return the end location.
     */
    public String getEnd() {
        return end;
    }

    /**
     * @return a new Route with a start and end location.
     */
    public Route(String start, String end) {
        this.start = start;
        this.end = end;
    }
}
