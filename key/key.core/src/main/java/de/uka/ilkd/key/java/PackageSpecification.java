package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.java.reference.PackageReferenceContainer;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.ExtList;

import javax.annotation.Nonnull;
import java.util.List;

/**
 * Package specification.
 * taken from COMPOST and changed to achieve an immutable structure
 */

public final class PackageSpecification extends JavaNonTerminalProgramElement implements PackageReferenceContainer {
    /**
     * Reference.
     */
    @Nonnull
    private final PackageReference reference;

    public PackageSpecification(PositionInfo pi, List<Comment> comments, @Nonnull PackageReference reference) {
        super(pi, comments);
        this.reference = reference;
    }

    /**
     * Package specification.
     *
     * @param children an ExtList with children
     */
    public PackageSpecification(ExtList children) {
        super(children);
        reference = children.get(PackageReference.class);
    }

    public PackageSpecification(PackageReference reference) {
        this(null, null, reference);
    }

    @Override
    @Nonnull
    public SourceElement getLastElement() {
        return reference;
    }


    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    @Override
    public int getChildCount() {
        int result = 0;
        result++;
        return result;
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     *                                        of bounds
     */

    @Override
    public ProgramElement getChildAt(int index) {
        if (index == 0) return reference;
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get package reference.
     *
     * @return the package reference.
     */

    @Override
    public PackageReference getPackageReference() {
        return reference;
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    @Override
    public void visit(Visitor v) {
        v.performActionOnPackageSpecification(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printPackageSpecification(this);
    }
}