#!/usr/bin/perl

use File::Find;
use File::Basename;
use Getopt::Long;
$module = "sleekex";
$cvs_module_rep = "/home/nguyenh2/cvs-repo";
$log_file = "/home/cristian/overnight_test/regression_tests/long-tests-result";
$output_file = $log_file;
$temp_output_dir = ".";
$crt = system "pwd";
$hip = '';
$sleek = '';
$examples_path_working = "sleekex/examples/working";
$examples_path_working_bags = "sleekex/examples/working_bags";
$examples_path_working_mult_specs = "sleekex/examples/working_mult_specs";
# list of file, nr of functions, function name, output, function name, output......
@hip_files=(["append.ss",1,"append","ERROR"]);
# list of file, string with result of each entailment....
@sleek_files=(
			["sleek1.slk","Valid.Fail."],
			["sleek2.slk","Valid.Fail."]);


open(LOGFILE, ">> $log_file") || die ("Could not open $log_file.\n");

$aux = `pwd`;
print LOGFILE "$aux";

@yest = `date +"%Y/%m/%d" -d "yesterday"`;$yest  = pop(@yest);$yest  = substr($yest, 0, 10);

@tomorrow = `date +"%Y/%m/%d" -d "tomorrow"`;$tomorrow = pop (@tomorrow);$tomorrow  = substr($tomorrow, 0, 10);

@today =`date +"%Y/%m/%d"`;$today = pop (@today);$today  = substr($today, 0, 10);

$aux = join "", 'cvs -d ',$cvs_module_rep,' rlog -S -d"', $yest, ' < ', $tomorrow, '" ',$module,' | grep "', $yest, '" | wc -l';
@wc = `$aux`;$wc = pop(@wc);

#if(not($wc>0)) {
#		print LOGFILE "$yest no changes\n";
#		print LOGFILE "----------\n";
#		close(LOGFILE);
#		exit(0);
#	}
	
print LOGFILE "$yest found changes $wc  deleting subdir: $temp_output_dir/$module\n";
$aux ="rm -r $temp_output_dir/$module";
$aux = system $aux;
$aux = system "cvs -d $cvs_module_rep checkout sleekex";
if ($aux!=0){
		print LOGFILE "error checkingout module $module\n";
		cleanup();
		print LOGFILE "----------\n";
		close(LOGFILE);
		exit(0);		
	}
print LOGFILE "cvs checked out $module\n";

$aux = system "cd $module/xml; make";
if ($aux!=0){
		print LOGFILE "error making the xml\n";
		cleanup();
		print LOGFILE "----------\n";	
		close(LOGFILE);
		exit(0);		
	}
$aux =system "cd $module; make hip;make sleek";
if ($aux!=0){
		print LOGFILE "error making sleekex\n";
		cleanup();
		print LOGFILE "----------\n";	
		close(LOGFILE);
		exit(0);		
	}
	
if ($optimized) {
  $hip = "$hip".'.opt';
  $sleek ="$sleek".'.opt -ee -filter';
}

$error_count = 0;
$error_files = "";

print LOGFILE "Making... OK\n Starting sleek tests:\n";
$sleek = "../../../sleek";
$tp = "omega"; $pth = "$examples_path_working/sleek";
call_find_s();

$tp = "mona";$pth = "$examples_path_working/sleek";
call_find_s();

print LOGFILE "Starting hip tests:\n";
$hip = "../../../hip";
$tp = "omega";$pth = "$examples_path_working/hip";
call_find_h();
$tp = "mona"; $pth = "$examples_path_working/hip";
call_find_h();

$hip = "../../hip";
$tp = "mona";$pth = "$examples_path_working_bags";
call_find_h();
$tp = "isabelle";$pth = "$examples_path_working_bags";
call_find_h();

$tp = "mona";$pth = "$examples_path_working_mult_specs";
call_find_h();
$tp = "isabelle";$pth = "$examples_path_working_mult_specs";
call_find_h();

if ($error_count > 0) {
 print LOGFILE "Total number of errors: $error_count in files: $error_files.\n";
}
else {
 print LOGFILE "No errors, all is fine.\n";
}


cleanup();
print LOGFILE "----------\n";	
close(LOGFILE);
exit(0);


sub call_find_s
{
print LOGFILE "using $tp\n";
find(\&sleek_process_file, "$pth");
}

sub call_find_h
{
print LOGFILE "using $tp\n";
find(\&hip_process_file, "$pth");
}

sub cleanup
{
	print LOGFILE "cleanup: removing checkedout dir: $temp_output_dir/$module\n";
	$aux ="rm -r $temp_output_dir/$module";
	$aux = system $aux;
}

sub hip_process_file {
  $file = $_;

  my $ext = (fileparse($file,'\..*'))[2];

  if ($ext eq ".ss") {
	print LOGFILE "Checking $file\n";
	print "$hip -tp $tp $file";
	eval {
        local $SIG{ALRM} = sub { `pkill hip;pkill mona;pkill isabelle;pkill hip`;die "alarm clock restart" };
        alarm 1800;
		my $output = `$hip -tp $tp $file 2>&1`;
        alarm 0;
    };
    if ($@ and $@ =~ /alarm clock restart/) {  $error_count++;$error_files = $error_files . "\n " . $file . " timed out ";print LOGFILE "!!!!!!!timed out\n"; print "!!!!!!!timed out"; }
	else {
		print "$output";
		#print LOGFILE "\n======================================\n";
		#print LOGFILE "$output";

		if ($output =~ /.*(e|E)rror.*/) {
		  print LOGFILE "Error found\n";
		  $error_count++;
		  $error_files = $error_files . " " . $file;
		  if ($stop) {
			exit(0);
		  }
		}
	}
  }
}

sub sleek_process_file  {
  $file = $_;

  my $ext = (fileparse($file,'\..*'))[2];

  if ($ext eq ".slk") {
        print LOGFILE "Checking $file\n";
		eval {
	        local $SIG{ALRM} = sub { `pkill sleek;pkill mona;pkill isabelle`;die "alarm clock restart" };
	        alarm 1800;
			 my $output = `$sleek -tp $tp $file 2>&1`;
	        alarm 0;
	    };
	    if ($@ and $@ =~ /alarm clock restart/) {  $error_count++;$error_files = $error_files . " " . $file;print "!!!!!!!timed out\n"; }
		else {
			print "$output";
	        #print LOGFILE "\n======================================\n";
	        #print LOGFILE "$output";

	        if (($output =~ /.*(e|E)rror.*/)||($output =~ /.*(f|F)ail.*/)) {
	          print LOGFILE "Error found\n";
	          $error_count++;
	          $error_files = $error_files . " " . $file;
	          if ($stop) {
	                exit(0);
	          }
	        }
		}
  }
}
