package org.key_project.starvoors.model;

public abstract class AbstractStaRVOOrSApplication {
   private final String file;
   
   private final int startLine;
   
   private final int startColumn;
   
   private final int endLine;
   
   private final int endColumn;

   public AbstractStaRVOOrSApplication(String file, int startLine, int startColumn, int endLine, int endColumn) {
      this.file = file;
      this.startLine = startLine;
      this.startColumn = startColumn;
      this.endLine = endLine;
      this.endColumn = endColumn;
   }

   public String getFile() {
      return file;
   }

   public int getStartLine() {
      return startLine;
   }

   public int getStartColumn() {
      return startColumn;
   }

   public int getEndLine() {
      return endLine;
   }

   public int getEndColumn() {
      return endColumn;
   }
}
