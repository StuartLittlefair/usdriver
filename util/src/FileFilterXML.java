package warwick.marsh.util;

import java.io.File;
import javax.swing.filechooser.FileFilter;

/**
 * File filter to select files of the form .xml
 * 
 */
public class FileFilterXML extends FileFilter {
    
    public boolean accept(File file) {
	return (file.isDirectory() || file.getName().endsWith(".xml"));
    }
    
    public String getDescription(){
	return "*.xml";
    }
    
}
