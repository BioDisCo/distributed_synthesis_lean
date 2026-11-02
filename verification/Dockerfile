# syntax=docker/dockerfile:1
# Build from the repository root: docker build -f verification/Dockerfile --target checker ... .
# Source snapshots, proof exports, and Docker images are not repository artifacts.
FROM rust:1.90.0-slim-trixie@sha256:7fa728f3678acf5980d5db70960cf8491aff9411976789086676bdf0c19db39e AS nanoda-build
RUN apt-get update && apt-get install -y --no-install-recommends git ca-certificates \
    && rm -rf /var/lib/apt/lists/*
RUN git init /src/nanoda && cd /src/nanoda \
    && git remote add origin https://github.com/ammkrn/nanoda_lib \
    && git fetch --depth 1 origin 4c544ed4099c8227f07d5de77ad1e69fb0740a27 \
    && git checkout --detach FETCH_HEAD && cargo build --release --locked

FROM debian:trixie-slim@sha256:d7e12182ce18b85b93007c1dedf31f2d29e01ccf3182cc4017c709b6259bc132 AS lean-base
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl elan git libatomic1 libgmp10 python3 zstd \
    && rm -rf /var/lib/apt/lists/* \
    && useradd --create-home --uid 1000 audit \
    && mkdir -p /opt/audit /work && chown audit:audit /work
ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/bin:${PATH}
ENV LEAN_NUM_THREADS=2

FROM lean-base AS checker-tools
RUN elan toolchain install leanprover/lean4:v4.34.0-rc2
ENV ELAN_TOOLCHAIN=leanprover/lean4:v4.34.0-rc2
RUN git init /opt/comparator && cd /opt/comparator \
    && git remote add origin https://github.com/leanprover/comparator \
    && git fetch --depth 1 origin 2312244ac716564a61cc0bf4e107d9abf1757a61 \
    && git checkout --detach FETCH_HEAD && lake build comparator
WORKDIR /opt/comparator
COPY verification/targets.json verification/ExportTargets.lean verification/checker_lean.py /opt/audit/
# Prepending our build directory avoids the exporter's unrelated Main module.
RUN lake env printenv LEAN_PATH > /opt/audit/lean-path \
    && python3 /opt/audit/checker_lean.py ExportTargets.lean > /opt/audit/export-targets.json

FROM checker-tools AS checker
COPY --from=nanoda-build /src/nanoda/target/release/nanoda_bin /usr/local/bin/nanoda_bin
COPY verification/CompareExports.lean verification/container.py verification/bundles.py /opt/audit/
USER audit
ENTRYPOINT ["python3", "/opt/audit/container.py", "compare"]

FROM lean-base AS proof-tools
RUN elan toolchain install leanprover/lean4:v4.30.0
RUN git init /opt/exporter && cd /opt/exporter \
    && git remote add origin https://github.com/leanprover/lean4export \
    && git fetch --depth 1 origin a3e35a584f59b390667db7269cd37fca8575e4bf \
    && git checkout --detach FETCH_HEAD && lake build lean4export

FROM proof-tools AS dependency-cache
ENV ELAN_TOOLCHAIN=leanprover/lean4:v4.30.0
COPY verification/cache_roots.py /opt/audit/
WORKDIR /opt/seed
COPY lean-toolchain lakefile.toml lake-manifest.json ./
COPY DistributedSynthesis.lean ./
COPY DistributedSynthesis/ ./DistributedSynthesis/
# Cache only Mathlib modules imported by this library and their dependencies.
RUN python3 /opt/audit/cache_roots.py \
    && chmod -R a+rX /opt/seed/.lake \
    && rm -rf /root/.cache/mathlib

FROM dependency-cache AS proof
COPY verification/ExportProject.lean /opt/exporter/ExportProject.lean
RUN printf '\n[[lean_exe]]\nname = "export_project"\nroot = "ExportProject"\nsupportInterpreter = true\n' >> /opt/exporter/lakefile.toml \
    && cd /opt/exporter && lake build export_project
COPY --from=checker-tools /opt/audit/export-targets.json /opt/audit/export-targets.json
COPY verification/targets.json verification/container.py verification/checker_lean.py \
    verification/bundles.py /opt/audit/
USER audit
WORKDIR /work
ENTRYPOINT ["python3", "/opt/audit/container.py", "export"]
