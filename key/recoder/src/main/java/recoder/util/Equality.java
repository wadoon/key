package recoder.util;

public interface Equality {
    Equality NATURAL = Order.NATURAL;

    Equality IDENTITY = Order.IDENTITY;

    boolean equals(Object paramObject1, Object paramObject2);
}
