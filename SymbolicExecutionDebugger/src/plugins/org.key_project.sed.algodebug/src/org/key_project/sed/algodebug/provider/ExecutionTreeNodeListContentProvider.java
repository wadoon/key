package org.key_project.sed.algodebug.provider;

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;


public class ExecutionTreeNodeListContentProvider implements IStructuredContentProvider{

   public ExecutionTreeNodeListContentProvider() {
   }

   @Override
   public void dispose() {      
   }

   @Override
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {      
   }

   @Override
   public Object[] getElements(Object inputElement) {
      return (Object[]) inputElement;
   }

}
