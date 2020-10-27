package recoder.convenience;

import recoder.java.ProgramElement;

public interface ProgramElementWalker {
    boolean next();

    ProgramElement getProgramElement();
}
