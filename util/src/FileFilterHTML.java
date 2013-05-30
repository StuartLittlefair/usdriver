package warwick.marsh.util;

import java.io.File;
import javax.swing.filechooser.FileFilter;

/**
 * File filter to select files of the form .html
 * 
 */
public class FileFilterHTML extends FileFilter {
    
    public boolean accept(File file) {
	return (file.isDirectory() || file.getName().endsWith(".html"));
    }
    
    public String getDescription(){
	return "*.html";
    }
    
}
