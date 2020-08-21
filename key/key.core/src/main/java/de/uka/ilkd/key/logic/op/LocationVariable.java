// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class represents proper program variables, which are not program
 * constants. See the description of the superclass ProgramVariable for
 * more information.
 */
public final class LocationVariable extends ProgramVariable
			            implements UpdateableOperator {
    private PositionInfo posInfo = PositionInfo.UNDEFINED;
    
    /**
     * This flag indicates that this location variable was created freshly for
     * proving purposes. E.e., the exception variable exc created for a standard
     * Java proof obligation is such a variable. The idea is to introduce a sound
     * approximation, i.e., if this flag is true, the variable is fresh for sure,
     * otherwise we do not know.
     */
    private final boolean isFresh;
    

    public LocationVariable(ProgramElementName name, KeYJavaType t, KeYJavaType containingType,
            boolean isStatic, boolean isModel, boolean isGhost, boolean isFinal, boolean isFresh) {
        super(name, t.getSort(), t, containingType, isStatic, isModel, isGhost, isFinal);
        this.isFresh = isFresh;
    }

    public LocationVariable(ProgramElementName name,
                        KeYJavaType        t,
                        KeYJavaType        containingType,
                        boolean            isStatic,
                        boolean            isModel,
                        boolean isGhost,
                        boolean isFinal) {
        this(name, t, containingType, isStatic, isModel, isGhost, isFinal, false);
    }
    
    public LocationVariable(ProgramElementName name,
            		    KeYJavaType        t,
            		    KeYJavaType        containingType,
            		    boolean            isStatic,
            		    boolean            isModel) {
        this(name, t, containingType, isStatic, isModel, false, false, false);
    }


    public LocationVariable(ProgramElementName name, KeYJavaType t) {
        this(name, t, null, false, false, false, false, false);
    }
    
    public LocationVariable(ProgramElementName name, KeYJavaType t, PositionInfo posInfo) {
        this(name, t, null, false, false, false, false, false);
        this.posInfo = posInfo;
    }


    public LocationVariable(ProgramElementName name, KeYJavaType t, boolean isFinal) {
        this(name, t, null, false, false, false, isFinal, false);
    }
    
    public LocationVariable(ProgramElementName name, KeYJavaType t, boolean isFinal, PositionInfo posInfo) {
        this(name, t, null, false, false, false, isFinal, false);
        this.posInfo = posInfo;
    }

    public LocationVariable(ProgramElementName name, KeYJavaType t, boolean isGhost, boolean isFinal) {
        this(name, t, null, false, false, isGhost, isFinal, false);
    }


    public LocationVariable(ProgramElementName name, Sort s) {
        super(name, s, null, null, false, false, false);
        this.isFresh = false;
    }

    @Override
    public void visit(de.uka.ilkd.key.java.visitor.Visitor v) {
        v.performActionOnLocationVariable(this);
    }
    
    @Override
    public PositionInfo getPositionInfo() {
        return posInfo;
    }

    /**
     * This flag indicates that this location variable was created freshly for
     * proving purposes. E.e., the exception variable exc created for a standard
     * Java proof obligation is such a variable. The idea is to introduce a sound
     * approximation, i.e., if this flag is true, the variable is fresh for sure,
     * otherwise we do not know.
     *
     * @return whether this {@link LocationVariable} is freshly introduced.
     */
    public boolean isFreshVariable() {
        return isFresh;
    }

    @Override
    public UpdateableOperator rename(Name name) {
        if (getKeYJavaType() != null) {
        return new LocationVariable(new ProgramElementName(name.toString()),
                                    getKeYJavaType(), getContainerType(),
                                    isStatic(), isModel());
        } else {
            return new LocationVariable(new ProgramElementName(name.toString()), sort());
        }
    }
}