// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2020 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.logic.op;

import java.util.Optional;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * A builder class for {@link LocationVariable}s. Simplifies the instantiation
 * of {@link LocationVariable}s in the presence of the many flags and values
 * that this class supports. Should be preferred over creating a
 * {@link LocationVariable} by a direct constructor call.
 * 
 * <p>
 * After creating an object of this class by using one of the two constructors
 * (one for variables of a {@link KeYJavaType}, and one where merely a
 * {@link Sort} is known), flags can be set by a cascade of calls to
 * {@link #staticVar()}, {@link #modelVar()}, {@link #ghostVar()},
 * {@link #finalVar()}, and {@link #freshVar()}. They set the flags
 * corresponding to their name to true. As a standard, all flags are false.
 * There also exist methods taking arguments like {@link #modelVar(boolean)}.
 * The optional container type and position info can be set by
 * {@link #containingType(KeYJavaType)} and {@link #posInfo(PositionInfo)},
 * respectively.
 * 
 * <p>
 * Finally, a {@link LocationVariable} object is created by a call to
 * {@link #create()}.
 * 
 * <p>
 * NOTE that objects of this class are immutable. You get a new object when
 * calling one of the setters.
 * 
 * @author Dominic Steinhoefel
 */
public class LocationVariableBuilder {
    private static final PositionInfo DEFAULT_POSINFO = PositionInfo.UNDEFINED;
    private static final KeYJavaType DEFAULT_CONTAINING_TYPE = null;

    private final ProgramElementName name;

    // Invariant: kjt.isPresent() <=> !sort.isPresent()

    private final Optional<KeYJavaType> kjt;
    private final Optional<Sort> sort;

    // Optional values:

    //   objects
    private final Optional<KeYJavaType> containingType;
    private final Optional<PositionInfo> posInfo;

    //   flags
    private boolean isStatic = false;
    private boolean isModel = false;
    private boolean isGhost = false;
    private boolean isFinal = false;
    private boolean isFresh = false;

    // ////////////////////////////////////// //
    //              Constructors              //
    // ////////////////////////////////////// //

    public LocationVariableBuilder(final ProgramElementName name, final KeYJavaType kjt) {
        this.name = name;
        this.kjt = Optional.of(kjt);
        this.sort = Optional.empty();
        this.containingType = Optional.empty();
        this.posInfo = Optional.empty();
    }

    public LocationVariableBuilder(final ProgramElementName name, final Sort sort) {
        this.name = name;
        this.kjt = Optional.empty();
        this.sort = Optional.of(sort);
        this.containingType = Optional.empty();
        this.posInfo = Optional.empty();
    }

    /**
     * Returns a {@link LocationVariableBuilder} with the present name and type /
     * sort, and flags, {@link PositionInfo} and containing {@link KeYJavaType} from
     * the given {@link LocationVariable}. Useful for quickly copying / renaming
     * etc. of {@link LocationVariable}s.
     * 
     * @param lv The {@link LocationVariable} from which to copy flags and optional
     * object properties.
     * @return The new {@link LocationVariableBuilder}.
     */
    public static LocationVariableBuilder fromLV(final LocationVariable lv) {
        if (lv.getKeYJavaType() == null) {
            return new LocationVariableBuilder(lv.getProgramElementName(), lv.sort())
                    .copyPropertiesFromLV(lv);
        } else {
            return new LocationVariableBuilder(lv.getProgramElementName(), lv.getKeYJavaType())
                    .copyPropertiesFromLV(lv);
        }
    }

    // ////////////////////////////////////// //
    //            Aux. Constructor            //
    // ////////////////////////////////////// //

    private LocationVariableBuilder(final ProgramElementName name, final Optional<KeYJavaType> kjt,
            final Optional<Sort> sort, final Optional<KeYJavaType> containingType,
            final Optional<PositionInfo> posInfo, final boolean isStatic, final boolean isModel,
            final boolean isGhost, final boolean isFinal, final boolean isFresh) {
        this.name = name;
        this.kjt = kjt;
        this.sort = sort;
        this.containingType = containingType;
        this.posInfo = posInfo;
        this.isStatic = isStatic;
        this.isModel = isModel;
        this.isGhost = isGhost;
        this.isFinal = isFinal;
        this.isFresh = isFresh;
    }

    // ////////////////////////////////////// //
    //              Flag Setters              //
    // ////////////////////////////////////// //

    public LocationVariableBuilder staticVar() {
        return staticVar(true);
    }

    public LocationVariableBuilder staticVar(final boolean isStatic) {
        return new LocationVariableBuilder( //
                name, kjt, sort, containingType, posInfo, isStatic, isModel, isGhost, isFinal,
                isFresh);
    }

    public LocationVariableBuilder modelVar() {
        return modelVar(true);
    }

    public LocationVariableBuilder modelVar(final boolean isModel) {
        return new LocationVariableBuilder( //
                name, kjt, sort, containingType, posInfo, isStatic, isModel, isGhost, isFinal,
                isFresh);
    }

    public LocationVariableBuilder ghostVar() {
        return ghostVar(true);
    }

    public LocationVariableBuilder ghostVar(final boolean isGhost) {
        return new LocationVariableBuilder( //
                name, kjt, sort, containingType, posInfo, isStatic, isModel, isGhost, isFinal,
                isFresh);
    }

    public LocationVariableBuilder finalVar() {
        return finalVar(true);
    }

    public LocationVariableBuilder finalVar(final boolean isFinal) {
        return new LocationVariableBuilder( //
                name, kjt, sort, containingType, posInfo, isStatic, isModel, isGhost, isFinal,
                isFresh);
    }

    public LocationVariableBuilder freshVar() {
        return freshVar(true);
    }

    public LocationVariableBuilder freshVar(final boolean isFresh) {
        return new LocationVariableBuilder( //
                name, kjt, sort, containingType, posInfo, isStatic, isModel, isGhost, isFinal,
                isFresh);
    }

    // ////////////////////////////////////// //
    //             Object Setters             //
    // ////////////////////////////////////// //

    public LocationVariableBuilder posInfo(final PositionInfo posInfo) {
        return new LocationVariableBuilder(name, kjt, sort, containingType,
                Optional.ofNullable(posInfo), isStatic, isModel, isGhost, isFinal, isFresh);
    }

    public LocationVariableBuilder containingType(final KeYJavaType containingType) {
        return new LocationVariableBuilder(name, kjt, sort, Optional.ofNullable(containingType),
                posInfo, isStatic, isModel, isGhost, isFinal, isFresh);
    }

    // ////////////////////////////////////// //
    //             Compound Setter            //
    // ////////////////////////////////////// //

    /**
     * Returns a {@link LocationVariableBuilder} with the present name and type /
     * sort, and flags, {@link PositionInfo} and containing {@link KeYJavaType} from
     * the given {@link LocationVariable}. Useful for quickly copying / renaming
     * etc. of {@link LocationVariable}s.
     * 
     * @param lv The {@link LocationVariable} from which to copy flags and optional
     * object properties.
     * @return The new {@link LocationVariableBuilder}.
     */
    public LocationVariableBuilder copyPropertiesFromLV(final LocationVariable lv) {
        final LocationVariableBuilder newLvb;

        if (sort.isPresent()) {
            newLvb = new LocationVariableBuilder(name, sort.get());
        } else {
            newLvb = new LocationVariableBuilder(name, kjt.get());
        }

        return newLvb.staticVar(lv.isStatic()).modelVar(lv.isModel()).ghostVar(lv.isGhost())
                .finalVar(lv.isFinal()).freshVar(lv.isFreshVariable()).posInfo(lv.getPositionInfo())
                .containingType(lv.getContainerType());
    }

    // ////////////////////////////////////// //
    //                 Creator                //
    // ////////////////////////////////////// //

    public LocationVariable create() {
        if (sort.isPresent()) {
            return new LocationVariable( //
                    name, sort.get(), posInfo.orElse(DEFAULT_POSINFO), isStatic, isModel, isGhost,
                    isFinal, isFresh);
        } else {
            return new LocationVariable( //
                    name, kjt.get(), containingType.orElse(DEFAULT_CONTAINING_TYPE),
                    posInfo.orElse(DEFAULT_POSINFO), isStatic, isModel, isGhost, isFinal, isFresh);
        }
    }

}
