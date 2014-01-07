package com.csvanefalk.keytestgen.targetmodels.publictransport.trains.train;

public class Train {

    /*@ public instance ghost non_null Wagon[] _wagons;
     */ Station nextStation;

    /*@ public normal_behavior
     *@ ensures \result == nextStation;
     *@ assignable \nothing;
     */
    public Station getNextStation() {
        return nextStation;
    }

    MyList /* @ non_null @ */wagons;

    public static Train createLocomotive() {
        Train t = new Train();
        t.nextStation = new Station("Central");
        return t;
    }

    Train() {
        wagons = new MyList();
    }

    /*@ public normal_behavior 
     *@ ensures \result == wagons.contains(w);
     */
    public boolean /* @ pure @ */ hasWagon(Wagon w) {
        return wagons.contains(w);
    }

    /*@ public normal_behavior
     *@ ensures hasWagon(w);
     *@ assignable _wagons;
     */
    void addWagon(Wagon w) {
        wagons.add(w);
    }

    /*@ public normal_behavior
     *@ ensures \result == (Wagon) wagons.get(i);
     *@ assignable \nothing;
     */
    public Wagon getWagon(int i) {
        return (Wagon) wagons.get(i);
    }

    /*@ ensures \result == wagons.size;
     *@ assignable \nothing;
     */
    public int length() {
        return wagons.size();
    }
}