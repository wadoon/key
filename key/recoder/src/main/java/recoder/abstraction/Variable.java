package recoder.abstraction;

public interface Variable extends ProgramModelElement {
    boolean isFinal();

    Type getType();
}
