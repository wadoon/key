package recoder.abstraction;

import java.util.List;

public interface ClassTypeContainer extends ProgramModelElement {
    List<? extends ClassType> getTypes();

    Package getPackage();

    ClassTypeContainer getContainer();
}
