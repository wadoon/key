//package de.uka.ilkd.key.speclang.jml.pretranslation;
//
//import java.util.LinkedHashMap;
//import java.util.Map;
//
//import de.uka.ilkd.key.collection.ImmutableList;
//import de.uka.ilkd.key.collection.ImmutableSLList;
//import de.uka.ilkd.key.ldt.HeapLDT;
//import de.uka.ilkd.key.logic.Name;
//import de.uka.ilkd.key.speclang.PositionedString;
//
//public class TextualJMLAbsCase extends TextualJMLSpecCase {
//    private Map<String, ImmutableList<PositionedString>>
//    defs = new LinkedHashMap<String, ImmutableList<PositionedString>>();
//
//	public TextualJMLAbsCase(ImmutableList<String> mods, Behavior behavior) {
//		super(mods, behavior);
//		for(Name hName : HeapLDT.VALID_HEAP_NAMES) {
//			defs.put(hName.toString(), ImmutableSLList.<PositionedString>nil());
//        }
//	}
//	
//	@Override
//    public void addDef(PositionedString ps) {
//        addGeneric(defs, ps);
//    }
//
//    @Override
//    public void addDef(ImmutableList<PositionedString> l) {
//        for(PositionedString ps : l) {
//           addDef(ps);
//        }
//    }
//    
//    @Override
//    public ImmutableList<PositionedString> getDefs() {
//        return defs.get(HeapLDT.BASE_HEAP_NAME.toString());
//    }
//    
//    @Override
//    public ImmutableList<PositionedString> getDefs(String hName) {
//        return defs.get(hName);
//    }
//    
//// TODO toString, equals, hashCode. Change SpecCase fields to protected?
//    
//    
//
//}
