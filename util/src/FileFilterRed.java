package warwick.marsh.util;

import java.io.File;
import javax.swing.filechooser.FileFilter;

/**
 * File filter to select files of the form *.red
 * 
 */
public class FileFilterRed extends FileFilter {
    
    public boolean accept(File file) {
	return (file.isDirectory() || file.getName().endsWith(".red"));
    }
    
    public String getDescription(){
	return "*.red";
    }
    
}
