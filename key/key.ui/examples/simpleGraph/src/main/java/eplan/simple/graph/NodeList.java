package eplan.simple.graph;

public class NodeList {

    /*@ public invariant array.length > firstFreeIndex; @*/

    private Node[] array;
    private int firstFreeIndex = 0;


    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures firstFreeIndex == 0;
      @*/
    public NodeList() {
        array = new Node[10];
        firstFreeIndex = 0;
    }


    /*@ public normal_behavior
      @ assignable \strictly_nothing;
      @ ensures \result == firstFreeIndex;
      @*/
    public int size() {
        return firstFreeIndex;
    }


    public void add (Node n) {
        if(array.length > firstFreeIndex + 1) {
            array[firstFreeIndex] = n;
        }
        else {
            int newLength = array.length + 10;
            Node[] newArray = new Node[newLength];
            for (int i = 0; i < array.length; i++) {
                newArray[i] = array[i];
            }
            newArray[firstFreeIndex] = n;
            array = newArray;
        }
        firstFreeIndex++;
    }


    /*@ public normal_behavior
      @ requires i >= 0 && i <= firstFreeIndex;
      @ assignable \strictly_nothing;
      @*/
    public Node get (int i) {
        return array[i];
    }


    public boolean contains (Node n) {
        if(getIndex(n) >= 0) {
            return true;
        }
        return false;
    }


    public int getIndex (Node n) {
        for (int i = 0; i < firstFreeIndex; i++) {
            if (array[i].equals(n)) {
                return i;
            }
        }
        return -1;
    }


    public void remove (int i) {
        for (int j = i; j < array.length - 1; j++) {
            array[j] = array[j+1];
        }
        array[array.length - 1] = null;
        firstFreeIndex--;
    }


    public String toString() {

        String returnval = "[";
        for (int i = 0; i < firstFreeIndex; i++) {
            returnval += array[i];
            if (i < firstFreeIndex - 1) {
                returnval += ",";
            }
        }
        returnval += "]";
        return returnval;
    }
}
