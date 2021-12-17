from ImageUtils.ObjectFetcher import ObjectFetcher
from ImageUtils.PlaneFetcher import PlaneFetcher
from ImageUtils.PlaneMarker import ReferenceMarker


class ReferencesFetcher:
    def __init__(self):
        self.object_fetcher = ObjectFetcher()
        self.plane_fetcher = PlaneFetcher()
        self.reference_marker = ReferenceMarker()

    def fetch(self, video, object_name):
        objects = self.object_fetcher.fetch_from_video(video, object_name)
        plane = self.plane_fetcher.fetch(objects[0].image, objects[0].borders)
        return self.reference_marker.getPlaneAndMask(plane, objects[0].borders)
