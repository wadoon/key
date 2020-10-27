package recoder.util;

public interface HashCode extends Equality {
    HashCode NATURAL = new Order.Natural();

    HashCode IDENTITY = new Order.Identity();

    int hashCode(Object paramObject);
}
