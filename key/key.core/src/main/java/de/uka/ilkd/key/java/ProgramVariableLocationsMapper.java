// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2010 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2019 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.java;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;

/**
 * Represents a bijective map from location variables to their representation as
 * a location (i.e., not a value). A location variable has roughly the same
 * relation to its location representation as a location set (o,f) to the value
 * "o.f". All functions in the map have the special type "ProgVar" which is
 * similar to the "Field" type and permits, e.g., quantification over program
 * variable locations.
 * 
 * Symbols of ProgVar sort should only be created by this class, in method
 * {@link #getAssociatedLocation(LocationVariable, Namespace)}.
 *
 * @author Dominic Steinhoefel
 */
public class ProgramVariableLocationsMapper {

    private final Map<LocationVariable, Function> locVarToLocVarSymbMap;
    private final Map<Function, LocationVariable> locVarSymbToLocVarMap;

    public ProgramVariableLocationsMapper() {
        this.locVarToLocVarSymbMap = new HashMap<>();
        this.locVarSymbToLocVarMap = new HashMap<>();
    }

    public ProgramVariableLocationsMapper(final ProgramVariableLocationsMapper other) {
        this.locVarToLocVarSymbMap = other.locVarToLocVarSymbMap;
        this.locVarSymbToLocVarMap = other.locVarSymbToLocVarMap;
    }

    /**
     * Returns the associated location function for the given variable. If none such
     * has been created yet, it is created freshly, the association is stored, and
     * the function is added to the given namespace.
     * 
     * @param variable The program variable for which to get the location
     *                 descriptor.
     * @param services The {@link Services} object.
     * @return The location descriptor.
     */
    public Function getAssociatedLocation(final LocationVariable variable,
            final Services services) {
        if (locVarToLocVarSymbMap.containsKey(variable)) {
            return locVarToLocVarSymbMap.get(variable);
        } else {
            final Name name = new Name(services.getTermBuilder().newName(variable.name().toString(),
                    services.getNamespaces()));
            final Function locVarSymb = new Function(name,
                    services.getTypeConverter().getLocSetLDT().getProgVarSort());
            
            associate(variable, locVarSymb);
            services.getNamespaces().functions().addSafely(locVarSymb);
            
            return locVarSymb;
        }
    }

    /**
     * Returns the {@link LocationVariable} for the given function describing the
     * associated location. If there has no association be stored yet, the result
     * might be empty, which however should not be the case if the given function
     * symbol has ProgVar type.
     * 
     * @param location The {@link LocationVariable} for which to retrieve the
     *                 location descriptor.
     * @return The associated location descriptor, or an empty {@link Optional} if
     *         none has been associated.
     */
    public Optional<LocationVariable> getAssociatedVariable(final Function location) {
        return Optional.ofNullable(locVarSymbToLocVarMap.get(location));
    }

    private void associate(final LocationVariable variable, final Function locVarSymb) {
        locVarToLocVarSymbMap.put(variable, locVarSymb);
        locVarSymbToLocVarMap.put(locVarSymb, variable);
    }

}
