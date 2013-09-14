package buses.travel;

/**
 * Represents a transportation route between two points (intermediary stops are
 * not modelled for the sake of simplicity).
 * 
 * @author christopher
 */
public class Route {

    String start;
    String end;

    public String getStart() {
        return start;
    }

    public String getEnd() {
        return end;
    }

    public Route(String start, String end) {
        this.start = start;
        this.end = end;
    }
}
