package recoder.service;

import recoder.ModelElement;
import recoder.abstraction.ClassType;
import recoder.convenience.Format;
import recoder.convenience.Formats;
import recoder.util.Debug;

import java.util.ArrayList;
import java.util.List;

abstract class ClassTypeTopSort implements Formats {
    private final List<ClassType> classesDFS = new ArrayList<ClassType>(32);

    private int[] indeg = new int[32];

    protected abstract List<ClassType> getAdjacent(ClassType paramClassType);

    private void initIndeg() {
        for (int i = 0; i < this.indeg.length; i++)
            this.indeg[i] = 0;
    }

    private int incrIndeg(int index) {
        while (index >= this.indeg.length) {
            int[] n = new int[this.indeg.length * 2];
            System.arraycopy(this.indeg, 0, n, 0, this.indeg.length);
            this.indeg = n;
        }
        this.indeg[index] = this.indeg[index] + 1;
        return this.indeg[index] + 1;
    }

    private int decrIndeg(int index) {
        this.indeg[index] = this.indeg[index] - 1;
        return this.indeg[index] - 1;
    }

    private void addClass(ClassType c) {
        if (c != null) {
            int idx = this.classesDFS.indexOf(c);
            if (idx == -1) {
                this.classesDFS.add(c);
                idx = this.classesDFS.size() - 1;
                List<ClassType> neighbors = getAdjacent(c);
                int s = neighbors.size();
                for (int i = 0; i < s; i++)
                    addClass(neighbors.get(i));
            }
            incrIndeg(idx);
        }
    }

    private void sort(ClassType c, List<ClassType> result) {
        if (c != null) {
            int idx = this.classesDFS.indexOf(c);
            if (idx == -1) {
                Debug.error(Format.toString("Could not find %c \"%s\" @%p in %f", c) + "\nList: " + Format.toString("%N", result) + "\n" + Debug.makeStackTrace());
                System.exit(0);
            }
            if (decrIndeg(idx) == 0) {
                result.add(c);
                List<ClassType> neighbors = getAdjacent(c);
                int s = neighbors.size();
                for (int i = 0; i < s; i++)
                    sort(neighbors.get(i), result);
            }
        }
    }

    public List<ClassType> getAllTypes(ClassType c) {
        initIndeg();
        this.classesDFS.clear();
        addClass(c);
        List<ClassType> result = new ArrayList<ClassType>(this.classesDFS.size());
        sort(c, result);
        if (result.size() < this.classesDFS.size())
            throw new RuntimeException("Cyclic inheritance detected!");
        return result;
    }
}
