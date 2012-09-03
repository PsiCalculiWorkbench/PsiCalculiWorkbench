#!/usr/bin/perl

use warnings;
use strict;
use Getopt::Std;


sub usage {
    print "Usage: $ENV{COMMANDEXEC} [-h] [-o <filename>] <instance name>\n";
}

my %opts;
getopts('o:h', \%opts);

if ($opts{h}) {
    usage;
    exit 0;
}

my $outfile;
if (exists $opts{o}) {
    if (defined $opts{o}) {
        $outfile = $opts{o};
    } else {
        print "output file not specified!\n";
        usage;
        exit 1;
    }
} else {
    $outfile = '-';
}

my $instance_name = $ARGV[0];
if (not defined $instance_name) {
    print "The instance name not given!\n";
    usage;
    exit 1;
}

if (!$ENV{PSI_WORKBENCH_HOME}) {
    print "The environment variable PSI_WORKBENCH_HOME is not set!\n";
    exit 1;
}

my $tmpl;
my $template_file = $ENV{PSI_WORKBENCH_HOME} . "/tools/template.ML";

if (-f $template_file) {
    local $/;
    open my $fh, "<", $template_file;
    $tmpl = <$fh>;
    close $fh;
    $tmpl =~ s/InstanceName___/$instance_name/g;
} else {
    print "Could not find the template file!\n";
    exit 1;
}


my $out;
if ($outfile eq '-') {
    $out = \*STDOUT;
} else {
    open $out, '>', $outfile;
}

print $out $tmpl;


if (not $outfile eq '-') {
    close $out;
}

