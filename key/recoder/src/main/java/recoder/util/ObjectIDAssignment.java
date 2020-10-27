package recoder.util;

public class ObjectIDAssignment {
    private static long currentId = 0L;

    private static final Index ids = new Index(HashCode.IDENTITY);

    public static long getID(Object o) {
        long res = ids.get(o);
        if (res == -1L) {
            res = currentId++;
            ids.put(o, res);
        }
        return res;
    }

    public static void releaseID(Object o) {
        ids.remove(o);
    }
}
