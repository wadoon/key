package com.csvanefalk.keytestgen.core.model.implementation.variable;

import java.util.Map;

/**
 * @author DoHuy
 * interpret array in function-style
 * */
public class ConcreteArrInterp {
   private Map<int[],Object> entries;
   private Object elseValue;
   /**
    * @param entries
    * @param elseValue
    */
   public ConcreteArrInterp(Map<int[], Object> entries,
         Object elseValue) {
      super();
      this.entries = entries;
      this.elseValue = elseValue;
   }
   public Map<int[], Object> getEntries() {
      return entries;
   }
   public void setEntries(Map<int[], Object> entries) {
      this.entries = entries;
   }
   public Object getElseValue() {
      return elseValue;
   }
   public void setElseValue(Object elseValue) {
      this.elseValue = elseValue;
   }   
   
   public String toString(){
      String result = "";
      for(int[] arguments: entries.keySet()){
         result += "[";
         for(int i=0;i<arguments.length;i++)
            result +=  arguments[i] + " ";
         result += "] -> " + entries.get(arguments).toString() + "\n";
      }
      result += "Else:-> " + elseValue.toString() + "\n";
      return result;
   }
}
