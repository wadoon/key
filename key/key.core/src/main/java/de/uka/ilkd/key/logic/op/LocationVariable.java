// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
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
 * constants. See the description of the superclass ProgramVariable for more
 * information.
 * 
 * <p>
 * To create objects of this class, use {@link LocationVariableBuilder}.
 */
public final class LocationVariable extends ProgramVariable implements UpdateableOperator {
    private PositionInfo posInfo = PositionInfo.UNDEFINED;

    /**
     * This flag indicates that this location variable was created freshly for
     * proving purposes. E.e., the exception variable exc created for a standard
     * Java proof obligation is such a variable. The idea is to introduce a sound
     * approximation, i.e., if this flag is true, the variable is fresh for sure,
     * otherwise we do not know.
     */
    private final boolean isFresh;

    LocationVariable(ProgramElementName name, KeYJavaType t, KeYJavaType containingType,
            PositionInfo posInfo, boolean isStatic, boolean isModel, boolean isGhost,
            boolean isFinal, boolean isFresh) {
        super(name, t.getSort(), t, containingType, isStatic, isModel, isGhost, isFinal);
        this.posInfo = posInfo;
        this.isFresh = isFresh;
    }

    LocationVariable(ProgramElementName name, Sort s, PositionInfo posInfo, boolean isStatic,
            boolean isModel, boolean isGhost, boolean isFinal, boolean isFresh) {
        super(name, s, null, null, isStatic, isModel, isGhost, isFinal);
        this.isFresh = isFresh;
        this.posInfo = posInfo;
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
        final LocationVariableBuilder lvb;
        final ProgramElementName peName = new ProgramElementName(name.toString());
        
        if (getKeYJavaType() != null) {
            lvb = new LocationVariableBuilder(peName, getKeYJavaType());
        } else {
            lvb = new LocationVariableBuilder(peName, sort());
        }

        return lvb //
                .containingType(getContainerType()) //
                .posInfo(posInfo) //
                .freshVar(isFresh) //
                .staticVar(isStatic()) //
                .modelVar(isModel()) //
                .finalVar(isFinal()) //
                .ghostVar(isGhost()) //
                .create();
    }
}