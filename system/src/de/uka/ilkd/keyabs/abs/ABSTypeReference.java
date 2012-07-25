package de.uka.ilkd.keyabs.abs;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.ProgramElementName;

public class ABSTypeReference extends ABSNonTerminalProgramElement implements TypeReference {

    private final KeYJavaType type;
    private final ProgramElementName typeName;
        
    
    public ABSTypeReference(KeYJavaType type) {
        this.typeName = new ProgramElementName(type.getName());
        this.type = type;
    }
        
    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        if (index == 0) {
            return typeName;
        }
        throw new IndexOutOfBoundsException();
    }

    @Override
    public int getTypeReferenceCount() {
        return 0;
    }

    @Override
    public TypeReference getTypeReferenceAt(int index) {
        throw new IndexOutOfBoundsException();
    }

    @Override
    public PackageReference getPackageReference() {
        throw new UnsupportedOperationException();
    }

    @Override
    public int getExpressionCount() {
        return 0;
    }

    @Override
    public Expression getExpressionAt(int index) {
        throw new IndexOutOfBoundsException();
    }

    @Override
    public String getName() {
        return typeName.toString();
    }

    @Override
    public ProgramElementName getProgramElementName() {
        return typeName;
    }

    @Override
    public ReferencePrefix getReferencePrefix() {
        return null;
    }

    @Override
    public int getDimensions() {
        return 0;
    }

    @Override
    public KeYJavaType getKeYJavaType() {
        return type;
    }

    @Override
    public void visit(ABSVisitor v) {
        v.performActionOnABSTypeReference(this);
    } 

    public String toString() {
    	return type.getFullName();
    }
 
}
