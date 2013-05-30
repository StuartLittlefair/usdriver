package warwick.marsh.ultracam;

// Simple class to store inforamtion on telescopes.
//
// 'name'      is the case sensitive name to be used for the telescope
// 'zeroPoint' is an array of mags giving 1 counts/sec at airmass zero for ugriz
// plateScale  is the scale in arcsec/pixel
// application is the name of an XML application to be used for this telescope

public class Telescope {

    public Telescope(String name, double[] zeroPoint, double plateScale, String application) {
	this.name        = name;
	this.zeroPoint   = zeroPoint;
	this.plateScale  = plateScale;
	this.application = application;
    }

    public String name;
    public double[] zeroPoint;
    public double plateScale;
    public String application;

};
