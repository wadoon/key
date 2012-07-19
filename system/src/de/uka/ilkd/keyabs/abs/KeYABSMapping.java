package de.uka.ilkd.keyabs.abs;

import java.util.HashMap;

import de.uka.ilkd.key.java.AbstractKeYProgramModelMapping;

public class KeYABSMapping extends AbstractKeYProgramModelMapping {

    public KeYABSMapping() {
        super();
    }

    /**
    * creates a KeYRecoderMapping object.
    * Used for cloning and testing.
    * @param map a HashMap mapping ProgramElements in Recoder to
    * ProgramElements in KeY
    * @param revMap the reverse map (KeY->Recoder)
    * @param parsedSpecial boolean indicating if the special classes have been parsed in
    */
    KeYABSMapping(HashMap map, HashMap revMap, boolean parsedSpecial){
        super(map, revMap, parsedSpecial);
    }

    
    @Override
    public KeYABSMapping copy() {
        return new KeYABSMapping((HashMap)map.clone(), (HashMap)revMap.clone(), parsedSpecial);
    }

}
