use std::hint::black_box;
use getargs::Argument;

#[inline(never)]
fn long_flag_ends_opts() -> bool {
    black_box("--long-flag-that-is-not-double-dash").ends_opts()
}

#[inline(never)]
fn ends_opts() -> bool {
    black_box("--").ends_opts()
}

#[inline(never)]
fn dash_ends_opts() -> bool {
    black_box("-").ends_opts()
}

#[inline(never)]
fn long_flag() -> Option<(&'static str, Option<&'static str>)> {
    black_box("--long-flag-with-no-value").parse_long_opt().unwrap()
}

#[inline(never)]
fn long_flag_blank_value() -> Option<(&'static str, Option<&'static str>)> {
    black_box("--long-flag-with-blank-value=").parse_long_opt().unwrap()
}

#[inline(never)]
fn long_flag_value() -> Option<(&'static str, Option<&'static str>)> {
    black_box("--long-flag-with-long-value=this-is-a-pretty-longish-value").parse_long_opt().unwrap()
}

#[inline(never)]
fn short_flag_cluster() -> Option<&'static str> {
    black_box("-verylongshortflagcluster").parse_short_cluster(true)
}

#[inline(never)]
fn short_flag_cluster_opt() -> (char, Option<&'static str>) {
    black_box("verylongshortflagcluster").consume_short_opt().unwrap()
}

#[inline(never)]
fn short_flag_cluster_val() -> &'static str {
    black_box("verylongshortflagcluster").consume_short_val()
}

#[inline(never)]
fn bytes_long_flag_ends_opts() -> bool {
    black_box(b"--long-flag-that-is-not-double-dash").ends_opts()
}

#[inline(never)]
fn bytes_ends_opts() -> bool {
    black_box(b"--").ends_opts()
}

#[inline(never)]
fn bytes_dash_ends_opts() -> bool {
    black_box(b"-").ends_opts()
}

#[inline(never)]
fn bytes_long_flag() -> Option<(&'static str, Option<&'static [u8]>)> {
    black_box(b"--long-flag-with-no-value").parse_long_opt().unwrap()
}

#[inline(never)]
fn bytes_long_flag_blank_value() -> Option<(&'static str, Option<&'static [u8]>)> {
    black_box(b"--long-flag-with-blank-value=").parse_long_opt().unwrap()
}

#[inline(never)]
fn bytes_long_flag_value() -> Option<(&'static str, Option<&'static [u8]>)> {
    black_box(b"--long-flag-with-long-value=this-is-a-pretty-longish-value").parse_long_opt().unwrap()
}

#[inline(never)]
fn bytes_short_flag_cluster() -> Option<&'static [u8]> {
    black_box(b"-verylongshortflagcluster").parse_short_cluster(true)
}

#[inline(never)]
fn bytes_short_flag_cluster_opt() -> (char, Option<&'static [u8]>) {
    black_box(b"verylongshortflagcluster").consume_short_opt().unwrap()
}

#[inline(never)]
fn bytes_short_flag_cluster_val() -> &'static [u8] {
    black_box(b"verylongshortflagcluster").consume_short_val()
}

fn main() {
    for _ in 0usize..1_000_000 {
        black_box(long_flag_ends_opts());
        black_box(ends_opts());
        black_box(dash_ends_opts());
        black_box(long_flag());
        black_box(long_flag_blank_value());
        black_box(long_flag_value());
        black_box(short_flag_cluster());
        black_box(short_flag_cluster_opt());
        black_box(short_flag_cluster_val());

        black_box(bytes_long_flag_ends_opts());
        black_box(bytes_ends_opts());
        black_box(bytes_dash_ends_opts());
        black_box(bytes_long_flag());
        black_box(bytes_long_flag_blank_value());
        black_box(bytes_long_flag_value());
        black_box(bytes_short_flag_cluster());
        black_box(bytes_short_flag_cluster_opt());
        black_box(bytes_short_flag_cluster_val());
    }
}
