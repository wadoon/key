package org.key_project.sed.algodebug.provider;

import org.eclipse.debug.core.DebugException;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;
import org.key_project.sed.core.model.ISENode;

public class ExecutionTreeNodeListLabelProvider implements ILabelProvider {

   public ExecutionTreeNodeListLabelProvider() {
      // TODO Auto-generated constructor stub
   }

   @Override
   public void addListener(ILabelProviderListener listener) {
      // TODO Auto-generated method stub

   }

   @Override
   public boolean isLabelProperty(Object element, String property) {
      // TODO Auto-generated method stub
      return false;
   }

   @Override
   public void removeListener(ILabelProviderListener listener) {
      // TODO Auto-generated method stub

   }

   @Override
   public Image getImage(Object element) {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public String getText(Object element) {
      try {
         return ((ISENode)element).getName().toString();
      }
      catch (DebugException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
      return null;
   }

   @Override
   public void dispose() {

   }

}
